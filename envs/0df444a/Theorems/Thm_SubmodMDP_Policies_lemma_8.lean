-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_8
-- name    : SubmodMDP.Policies.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:32.128232+00:00
-- url     : https://prove2.me/theorems/484545fc-d889-49a5-81b3-ee3adca29dfd
-- title:
--   Lemma 8 — initial bound: $U$, $x$ and $c_D$ with $\mathbb E_{\mathrm{RRR}(x)}[f]\ge f(U)/(nc_D)$
-- statement:
--   Let $G$ be a layered graph with $H=d^r$ ($d\ge2$) and $n=|V|$ vertices, $f:2^V\to\mathbb Q_{\ge0}$ monotone submodular, and $D\in\mathbb Z^{m\times\binom{V}{\le r+1}}$, $b\in\mathbb Z^m$ with $Q^{(r)}\cap\{y:Dy\le b\}\ne\emptyset$. In time $n^{O(r)}\langle D,b\rangle^{O(1)}$ one can compute $U\subseteq V$, a point $x\in Q^{(r)}$ and a positive integer
--   $$c_D\le 2^{\,n^{O(r)}\langle D,b\rangle^{O(1)}}$$
--   such that $Dx\le b$, $\mathbb P_{\mathrm{OPT}\sim\mathcal O}[u\in\mathrm{OPT}]=0$ for every $u\in V\setminus U$ and every distribution $\mathcal O$ over layer-spanning paths with $\mathbb E_{\mathcal O}[D\mathbf 1^{(r)}_{\mathrm{OPT}}]\le b$, and
--   $$\mathbb E_{P\sim\mathrm{RRR}(x)}[f(P)]\ \ge\ \frac{1}{n\,c_D}\,f(U).$$
--
--   The lemma brackets the optimum and fixes the range of the binary search in the proof of Lemma 7.
--
--   Differences from the source:
--   - encoding: time n^{O(r)}⟨D,b⟩^{O(1)} and c_D ≤ 2^{n^{O(r)}⟨D,b⟩^{O(1)}} → ∃ absolute c: a deterministic program halting within B = (n+1)^{c(r+1)}(⟨D,b⟩+1)^c on every input, and 1 ≤ c_D ≤ 2^B; reason: instantiation of O(·) with one explicit constant for both bounds; "we can compute" is a deterministic computation; c_D is a denominator bound, a positive integer
--   - reading: running time as the number of word-RAM operations, words large enough to store every input value and every value of f (footnote 2); no fixed instruction set or randomness primitive → the randomized value-oracle integer RAM of SubmodMDP.Policies.Machine: integer registers, +, -, ×, floor division/modulus, indirect addressing, jumps, a value-oracle query and rand M (uniform on {0,…,M-1}); an instruction on operands of k words of w bits costs (1+k)², a query on m indices (1+m)(1+k)², w covers ⌈log₂(input length+2)⌉, every input integer and every numerator/denominator of f; every run must halt within the bound; reason: footnote 2 fixes only the word size; every instruction is simulable on a w-bit word RAM in O(cost) operations, so a bound here implies the paper's; exact sampling (rand M) is needed because with fair coins only, an exact law with probabilities 1/3 cannot be produced within a worst-case bound, which would falsify the exact distributional claims
--   - reading: f : 2^V → ℝ≥0 monotone submodular, given by a value oracle → f : Finset V → ℚ with 0 ≤ f, monotone and submodular after the cast to ℝ, accessed only through the machine's query instruction; reason: footnote 2 requires every value of f to fit in a word, which forces a finite representation
--   - encoding: U, x, c_D as mathematical objects → output decoded from a fixed format (indicator of U, coordinates of x, c_D); reason: a program writes an integer list
--   - encoding: x ∈ ℝ^{(V choose ≤ r+1)} → a function on all vertex sets of which only the coordinates with |I| ≤ r+1 are read; reason: coordinates outside the index set are never used by Q^(r), RRR or the linear functions; same instances
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 8, p. 15 (PDF p. 16); setting of §2.4, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SubmodMDP.Policies

open NonmonotoneSubmod.Shared SubsamplingSM.Offline

/-- Lemma 8 (PDF p. 15), with `n^{O(r)} ⟨D,b⟩^{O(1)}` instantiated as
`(n+1)^{c(r+1)} (⟨D,b⟩+1)^c`, `n = |V|`. A deterministic program computes, within that cost,
`U ⊆ V`, a rational `x ∈ Q^(r)` with `Dx ≤ b`, and a positive integer
`c_D ≤ 2^{(n+1)^{c(r+1)} (⟨D,b⟩+1)^c}` such that `P_{OPT∼O}[u ∈ OPT] = 0` for every
`u ∈ V ∖ U` and every distribution `O` over layer-spanning paths with `E_O[D 1^(r)_OPT] ≤ b`, and
`E_{P∼RRR(x)}[f(P)] ≥ f(U) / (n c_D)`. -/
theorem lemma_8 :
    ∃ c : ℕ, ∃ Alg : Program, Alg.Deterministic ∧
    ∀ (G : LGraph), G.WF → ∀ d r : ℕ, 2 ≤ d → G.H = d ^ r →
    ∀ f : Finset (Fin G.N) → ℚ, (∀ X, 0 ≤ f X) → IsMonotoneSetFn (fun X => (f X : ℝ)) →
      Submodular (fun X => (f X : ℝ)) →
    ∀ (m : ℕ) (D : Fin m → Finset (Fin G.N) → ℤ) (b : Fin m → ℤ),
      (∃ y : Finset (Fin G.N) → ℝ, InQ G r y ∧ SatDb r m D b y) →
    let O : Oracle := ⟨G.N, f⟩
    let inp : List ℤ := encGraph G ++ [(d : ℤ), (r : ℤ)] ++ encDb G.N r m D b
    let B : ℕ := (G.N + 1) ^ (c * (r + 1)) * (sizeDb G.N r m D b + 1) ^ c
    HaltsWithin Alg O (wordLen inp O) inp B ∧
    ∀ σ : List ℤ, some σ ∈ (outLaw Alg O (wordLen inp O) inp B).support →
      ∃ U : Finset (Fin G.N), ∃ x : Finset (Fin G.N) → ℚ, ∃ cD : ℕ,
        decodeL8 G.N r σ = some (U, x, cD) ∧
        1 ≤ cD ∧ cD ≤ 2 ^ B ∧
        InQ G r (fun I => (x I : ℝ)) ∧ SatDb r m D b (fun I => (x I : ℝ)) ∧
        (∀ Od : PMF (List (Fin G.N)), FeasibleDist G r m D b Od →
          ∀ u : Fin G.N, u ∉ U → Od.toOuterMeasure {P | u ∈ P} = 0) ∧
        (f U : ℝ) / ((G.N : ℝ) * (cD : ℝ)) ≤ pmfExp (RRR G d r (fun I => (x I : ℝ))) (fOpt f) := by sorry

end SubmodMDP.Policies
