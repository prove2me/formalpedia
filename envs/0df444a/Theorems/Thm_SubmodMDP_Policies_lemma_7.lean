-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_7
-- name    : SubmodMDP.Policies.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:31.483265+00:00
-- url     : https://prove2.me/theorems/1eff2118-2928-425e-b0d0-ca5cf8ec8584
-- title:
--   Lemma 7 — round-or-cut with linear constraints
-- statement:
--   Let $G$ be a layered graph with $V=V_1\cup\dots\cup V_H$, $H=d^r$ ($d\ge2$), $n=|V|$, let $f:2^V\to\mathbb Q_{\ge0}$ be monotone submodular, let $Dy\le b$ ($D,b$ integer) be constraints on $y\in\mathbb R^{\binom{V}{\le r+1}}$ with $Q^{(r)}\cap\{y:Dy\le b\}\ne\emptyset$, and let $\varepsilon>0$. There is a randomized procedure running in time $n^{O(r)}\langle D,b\rangle^{O(1)}$ that returns $x\in Q^{(r)}$ with $Dx\le b$ and, with probability at least $1-n^{-1/\varepsilon}$, the returned $x$ satisfies
--   $$\mathbb E_{P\sim\mathrm{RRR}(x)}[f(P)]\ \ge\ \frac{1-\varepsilon}{(d-1)(r+1)}\,\mathbb E_{\mathrm{OPT}\sim\mathcal O}[f(\mathrm{OPT})]$$
--   for every distribution $\mathcal O$ over layer-spanning paths with $\mathbb E_{\mathrm{OPT}\sim\mathcal O}[D\mathbf 1^{(r)}_{\mathrm{OPT}}]\le b$.
--
--   This is the algorithmic core used for both Theorem 1 and Theorem 2; in Theorem 2 the constraints $Dy\le b$ are (7).
--
--   Differences from the source:
--   - encoding: randomized n^{O(r)}⟨D,b⟩^{O(1)} time → ∀ ε > 0, ∃ c and a program whose every run halts within (n+1)^{c(r+1)}(⟨D,b⟩+1)^c; reason: instantiation of O(·); the constant comes after ε ("let ε > 0" precedes the claim)
--   - reading: running time as the number of word-RAM operations, words large enough to store every input value and every value of f (footnote 2); no fixed instruction set or randomness primitive → the randomized value-oracle integer RAM of SubmodMDP.Policies.Machine: integer registers, +, -, ×, floor division/modulus, indirect addressing, jumps, a value-oracle query and rand M (uniform on {0,…,M-1}); an instruction on operands of k words of w bits costs (1+k)², a query on m indices (1+m)(1+k)², w covers ⌈log₂(input length+2)⌉, every input integer and every numerator/denominator of f; every run must halt within the bound; reason: footnote 2 fixes only the word size; every instruction is simulable on a w-bit word RAM in O(cost) operations, so a bound here implies the paper's; exact sampling (rand M) is needed because with fair coins only, an exact law with probabilities 1/3 cannot be produced within a worst-case bound, which would falsify the exact distributional claims
--   - reading: f : 2^V → ℝ≥0 monotone submodular, given by a value oracle → f : Finset V → ℚ with 0 ≤ f, monotone and submodular after the cast to ℝ, accessed only through the machine's query instruction; reason: footnote 2 requires every value of f to fit in a word, which forces a finite representation
--   - reading: with probability 1 − n^{−1/ε}, the returned x satisfies … for any distribution O … → the probability (over the program's coins) of the event that the decoded x satisfies the inequality for every feasible O is at least 1 − n^{−1/ε}; x ∈ Q^(r) and Dx ≤ b on every run; reason: "with probability p" for a guarantee of a randomized algorithm means at least p; the good event is one event about x
--   - encoding: the returned x → decoded from the output in a fixed format (coordinates of x in a fixed order); reason: a program writes an integer list
--   - encoding: x ∈ ℝ^{(V choose ≤ r+1)} → a function on all vertex sets of which only the coordinates with |I| ≤ r+1 are read; reason: coordinates outside the index set are never used by Q^(r), RRR or the linear functions; same instances
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 7, pp. 13–14 (PDF pp. 14–15)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SubmodMDP.Policies

open NonmonotoneSubmod.Shared SubsamplingSM.Offline

/-- Lemma 7 (PDF pp. 13–14), with `n^{O(r)} ⟨D,b⟩^{O(1)}` instantiated as
`(n+1)^{c(r+1)} (⟨D,b⟩+1)^c` (`c` may depend on the fixed `ε`), `n = |V|`. For every `ε > 0`
there is a randomized program whose every run, on a layered graph with `H = d^r`, a non-negative
monotone submodular `f` (value oracle) and integer constraints `Dy ≤ b` with
`Q^(r) ∩ {Dy ≤ b} ≠ ∅`, halts within that cost and returns a rational `x ∈ Q^(r)` with `Dx ≤ b`;
and with probability at least `1 - n^{-1/ε}` the returned `x` satisfies
`E_{P∼RRR(x)}[f(P)] ≥ (1-ε)/((d-1)(r+1)) · E_{OPT∼O}[f(OPT)]` for every distribution `O` over
layer-spanning paths with `E_O[D 1^(r)_OPT] ≤ b`. -/
theorem lemma_7 (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℕ, ∃ Alg : Program,
    ∀ (G : LGraph), G.WF → ∀ d r : ℕ, 2 ≤ d → G.H = d ^ r →
    ∀ f : Finset (Fin G.N) → ℚ, (∀ X, 0 ≤ f X) → IsMonotoneSetFn (fun X => (f X : ℝ)) →
      Submodular (fun X => (f X : ℝ)) →
    ∀ (m : ℕ) (D : Fin m → Finset (Fin G.N) → ℤ) (b : Fin m → ℤ),
      (∃ y : Finset (Fin G.N) → ℝ, InQ G r y ∧ SatDb r m D b y) →
    let O : Oracle := ⟨G.N, f⟩
    let inp : List ℤ := encGraph G ++ [(d : ℤ), (r : ℤ)] ++ encDb G.N r m D b
    let B : ℕ := (G.N + 1) ^ (c * (r + 1)) * (sizeDb G.N r m D b + 1) ^ c
    let μ := outLaw Alg O (wordLen inp O) inp B
    HaltsWithin Alg O (wordLen inp O) inp B ∧
    (∀ σ : List ℤ, some σ ∈ μ.support →
      ∃ x : Finset (Fin G.N) → ℚ, decodePoint G.N (r + 1) σ = some x ∧
        InQ G r (fun I => (x I : ℝ)) ∧ SatDb r m D b (fun I => (x I : ℝ))) ∧
    ENNReal.ofReal (1 - (G.N : ℝ) ^ (-(1 / ε))) ≤
      μ.toOuterMeasure {o | ∃ σ x, o = some σ ∧ decodePoint G.N (r + 1) σ = some x ∧
        ∀ Od : PMF (List (Fin G.N)), FeasibleDist G r m D b Od →
          (1 - ε) / (((d : ℝ) - 1) * ((r : ℝ) + 1)) * pmfExp Od (fun P => (f P.toFinset : ℝ)) ≤
            pmfExp (RRR G d r (fun I => (x I : ℝ))) (fOpt f)} := by sorry

end SubmodMDP.Policies
