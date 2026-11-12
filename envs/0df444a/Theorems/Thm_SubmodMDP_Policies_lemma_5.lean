-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_5
-- name    : SubmodMDP.Policies.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:30.459091+00:00
-- url     : https://prove2.me/theorems/9f96c20c-bcbf-4912-ac4a-aa5c4326f905
-- title:
--   Lemma 5 — conditioned rounded paths and a linear upper bound on $f$
-- statement:
--   Let $d\in\mathbb Z_{\ge2}$ and $r\in\mathbb Z_{\ge0}$ with $H=d^r$, let $G$ be a layered graph with $n=|V|$ vertices, let $x\in Q^{(r)}$ be rational, and let $f:2^V\to\mathbb Q_{\ge0}$ be monotone submodular. There is a randomized algorithm running in time $n^{O(r)}$ that returns one random path $P_t\sim\mathrm{RRR}^{|t}(x)$ (the law of $\mathrm{RRR}(x)$ conditioned on $t\in P$) for each $t\in V_H$ with $x_t>0$, and a linear function $\ell(y)=\sum_{|I|\le r+1}\ell_Iy_I$, such that
--
--   1. the path $\bar P$, set equal to $P_t$ with probability $x_t$, is distributed as $\mathrm{RRR}(x)$;
--   2. $$\mathbb E[f(\bar P)]=\sum_{t\in V_H:\,x_t>0}x_t\,\mathbb E[f(P_t)]\ \ge\ \frac{\mathbb E[\ell(x)]}{(d-1)(r+1)};$$
--   3. with probability one, $\ell(\mathbf 1^{(r)}_{P'})\ge f(P')$ for all layer-spanning paths $P'$;
--   4. with probability one, $\ell_I\in[0,f(V)]$ for all $|I|\le r+1$.
--
--   Here the paths $P_t$ and $\ell$ are outputs of one run, and the expectations are over the algorithm's randomness. This is the round-or-cut engine of the paper: either the rounded path is good, or $\ell$ is a valid cut violated by $x$.
--
--   Differences from the source:
--   - encoding: randomized n^{O(r)} time, n = |V| → ∃ absolute c, every run halts with cost at most (n+1)^{c(r+1)}; reason: instantiation of O(·) with an explicit constant; (n+1) avoids the degenerate base n = 1
--   - reading: running time as the number of word-RAM operations, words large enough to store every input value and every value of f (footnote 2); no fixed instruction set or randomness primitive → the randomized value-oracle integer RAM of SubmodMDP.Policies.Machine: integer registers, +, -, ×, floor division/modulus, indirect addressing, jumps, a value-oracle query and rand M (uniform on {0,…,M-1}); an instruction on operands of k words of w bits costs (1+k)², a query on m indices (1+m)(1+k)², w covers ⌈log₂(input length+2)⌉, every input integer and every numerator/denominator of f; every run must halt within the bound; reason: footnote 2 fixes only the word size; every instruction is simulable on a w-bit word RAM in O(cost) operations, so a bound here implies the paper's; exact sampling (rand M) is needed because with fair coins only, an exact law with probabilities 1/3 cannot be produced within a worst-case bound, which would falsify the exact distributional claims
--   - reading: f : 2^V → ℝ≥0 monotone submodular, given by a value oracle → f : Finset V → ℚ with 0 ≤ f, monotone and submodular after the cast to ℝ, accessed only through the machine's query instruction; reason: footnote 2 requires every value of f to fit in a word, which forces a finite representation
--   - encoding: inputs x, G and outputs (P_t)_t, ℓ as mathematical objects → x, G encoded as integer lists; outputs decoded from a fixed format (paths of the support vertices of V_H in index order, then the coefficients of ℓ); reason: a program reads and writes integer lists; the formats are fixed and documented
--   - encoding: P_t ∼ RRR^{|t}(x) → P[P_t ∈ A] = P_{RRR(x)}[P ∈ A and t ∈ P] / x_t for every set A of vertex lists; reason: definition of the conditional law; P_{RRR(x)}[t ∈ P] = x_t by Lemma 4
--   - encoding: bullets 3 and 4 hold with probability 1 → they hold for every output of a run with positive probability; reason: the output law has finite support, so probability one is the same as every run in the support
--   - encoding: x ∈ ℝ^{(V choose ≤ r+1)} → a function on all vertex sets of which only the coordinates with |I| ≤ r+1 are read; reason: coordinates outside the index set are never used by Q^(r), RRR or the linear functions; same instances
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 5, p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SubmodMDP.Policies

open NonmonotoneSubmod.Shared SubsamplingSM.Offline

/-- Lemma 5 (PDF p. 9), with `n^{O(r)}` instantiated as `(n+1)^{c(r+1)}`, `n = |V|`.
There is one program `Alg` and an absolute constant `c` such that, for every layered graph with
`H = d^r` (`d ≥ 2`), every rational `x ∈ Q^(r)` and every non-negative monotone submodular
rational-valued `f` (accessed through its value oracle), every run of `Alg` on the encoded
`(G, d, r, x)` halts within cost `(n+1)^{c(r+1)}` and outputs paths `P_t` (`t ∈ V_H`, `x_t > 0`)
and a linear function `ℓ` such that:
* `P_t ∼ RRR^{|t}(x)` for each such `t`, and the mixture `P̄` (`P̄ = P_t` with probability `x_t`)
  is distributed as `RRR(x)`;
* `E[f(P̄)] = ∑_t x_t E[f(P_t)] ≥ E[ℓ(x)] / ((d-1)(r+1))`;
* on every run, `ℓ(1^(r)_{P'}) ≥ f(P')` for all layer-spanning paths `P'`;
* on every run, `ℓ_I ∈ [0, f(V)]` for all `|I| ≤ r+1`. -/
theorem lemma_5 :
    ∃ c : ℕ, ∃ Alg : Program,
    ∀ (G : LGraph), G.WF → ∀ d r : ℕ, 2 ≤ d → G.H = d ^ r →
    ∀ x : Finset (Fin G.N) → ℚ, InQ G r (fun I => (x I : ℝ)) →
    ∀ f : Finset (Fin G.N) → ℚ, (∀ X, 0 ≤ f X) → IsMonotoneSetFn (fun X => (f X : ℝ)) →
      Submodular (fun X => (f X : ℝ)) →
    let O : Oracle := ⟨G.N, f⟩
    let inp : List ℤ := encGraph G ++ [(d : ℤ), (r : ℤ)] ++ encPoint G.N (r + 1) x
    let B : ℕ := (G.N + 1) ^ (c * (r + 1))
    let μ := outLaw Alg O (wordLen inp O) inp B
    let path : List ℤ → Fin G.N → List (Fin G.N) := fun σ t =>
      match decodeL5 G r x σ with
      | some res => res.1 t
      | none => []
    let coef : List ℤ → Finset (Fin G.N) → ℚ := fun σ I =>
      match decodeL5 G r x σ with
      | some res => res.2 I
      | none => 0
    let supp : Finset (Fin G.N) := Finset.univ.filter (fun t => G.layer t = G.H ∧ 0 < x {t})
    let ρ := RRR G d r (fun I => (x I : ℝ))
    HaltsWithin Alg O (wordLen inp O) inp B ∧
    (∀ σ : List ℤ, some σ ∈ μ.support →
      (decodeL5 G r x σ).isSome ∧
      (∀ P' : List (Fin G.N), IsLSPath G P' →
        (f P'.toFinset : ℝ) ≤ linEval r (fun I => (coef σ I : ℝ)) (liftInd P'.toFinset)) ∧
      (∀ I : Finset (Fin G.N), I.card ≤ r + 1 → 0 ≤ coef σ I ∧ coef σ I ≤ f Finset.univ)) ∧
    (∀ t ∈ supp, ∀ A : Set (List (Fin G.N)),
      μ.toOuterMeasure {o | ∃ σ, o = some σ ∧ path σ t ∈ A} =
        ρ.toOuterMeasure {o | ∃ P, o = some P ∧ P ∈ A ∧ t ∈ P} / ENNReal.ofReal (x {t})) ∧
    (∀ A : Set (List (Fin G.N)),
      ∑ t ∈ supp, ENNReal.ofReal (x {t}) * μ.toOuterMeasure {o | ∃ σ, o = some σ ∧ path σ t ∈ A} =
        ρ.toOuterMeasure {o | ∃ P, o = some P ∧ P ∈ A}) ∧
    pmfExp ρ (fOpt f) = ∑ t ∈ supp, (x {t} : ℝ) * outExp μ (fun σ => (f (path σ t).toFinset : ℝ)) ∧
    outExp μ (fun σ => linEval r (fun I => (coef σ I : ℝ)) (fun I => (x I : ℝ))) /
        (((d : ℝ) - 1) * ((r : ℝ) + 1)) ≤
      ∑ t ∈ supp, (x {t} : ℝ) * outExp μ (fun σ => (f (path σ t).toFinset : ℝ)) := by sorry

end SubmodMDP.Policies
