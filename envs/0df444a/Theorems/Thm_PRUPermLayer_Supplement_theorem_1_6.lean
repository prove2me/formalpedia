-- Prove2me | Theorems.Thm_PRUPermLayer_Supplement_theorem_1_6
-- name    : PRUPermLayer.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:41:42.617144+00:00
-- url     : https://prove2.me/theorems/46508a8e-d535-4741-9611-e83c7395391e
-- title:
--   Theorem 1.6 — mixed-access attack on $L_1PL_2$: two forward and two inverse queries give advantage $\ge1/36-3/N^2$ ($\ge1/9-3/N^2$ for Clifford layers)
-- statement:
--   Let $n\ge2$ and $N=2^n$. There is an algorithm, independent of the oracle, that makes two forward and two inverse queries without controlled access and distinguishes every unitary
--   $$U=L_1\,P\,L_2,$$
--   where $L_1=C_1\otimes\cdots\otimes C_n$ and $L_2=C'_1\otimes\cdots\otimes C'_n$ are single-qubit product unitaries and $P$ is a permutation of the computational basis, from a Haar-random unitary with advantage at least
--   $$\frac1{36}-\frac3{N^2},\qquad\text{that is,}\qquad \Big|\Pr[A^{U}=1]-\mathbb E_{V\sim\mathrm{Haar}}\Pr[A^{V}=1]\Big|\ \ge\ \frac1{36}-\frac3{N^2}.$$
--   A second such algorithm achieves advantage at least
--   $$\frac19-\frac3{N^2}$$
--   for every such $U$ whose layers $L_1$ and $L_2$ consist of Clifford gates.
--
--   Here an algorithm with forward and inverse access applies $U$ or $U^\dagger$ to its query register at each query, with arbitrary oracle-independent unitaries on the query register and a workspace in between, and then measures one output bit. The layers and the permutation are arbitrary and fixed: nothing is random except the Haar oracle in the comparison. With uniformly random Clifford layers $L_1PL_2$ is secure against forward queries alone and against inverse queries alone, so the theorem shows that combining the two directions gives an algorithm much more power.
--
--   The bounds are as printed and are positive for $n\ge4$ (first algorithm) and $n\ge3$ (second); for smaller $n$ they are negative and the corresponding claim holds trivially.
--
--   **Formalization Note** "Independent of the oracle" is the quantifier order: each algorithm is chosen before $L_1,P,L_2$. Algorithms are the fixed-direction mixed-access subclass `MixAlg n 4` (any workspace, any final effect; the oracle enters only as $U\otimes I$ or $U^\dagger\otimes I$, so there is no controlled access), with exactly two forward and two inverse queries in a fixed order chosen by the algorithm. The layers are the published `layerUnitary` of arbitrary $C_i\in U(2)$, $P$ is the published `permUnitary` of an arbitrary permutation, and a Clifford layer has every factor satisfying `IsCliffordGate` (global phases allowed). Each existential also asserts that the acceptance probability is Haar-integrable (it is continuous and bounded on the compact group), so that the Haar term is a genuine expectation.
--
--   Differences from the source:
--   - generalization: mixed-access directions may be chosen classically from earlier measurement outcomes → the witnessing algorithm has one fixed direction sequence; reason: fixed-direction algorithms are valid mixed-access algorithms, and the paper's exhibited attack uses the fixed order $U^\dagger,U,U^\dagger,U$
--   - encoding: the advantage against a Haar-random unitary → |Pr[A^U = 1] − ∫ Pr[A^V = 1] dHaar(V)| together with Haar-integrability of V ↦ Pr[A^V = 1]; reason: the acceptance probability is continuous and bounded on the compact group, so the conjunct holds for every algorithm and only rules out the junk value 0 of a Bochner integral
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), Theorem 1.6, p.4 (PDF p.6); proof §8.2, pp.26–27 (PDF pp.28–29), Appendix A, Lemma A.1, pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_PRUPermLayer_haar
import Definitions.Def_PRUPermLayer_permUnitary
import Definitions.Def_PRUPermLayer_layerUnitary
import Definitions.Def_PRUPermLayer_Supplement_mixAcceptProb
import Definitions.Def_PRUPermLayer_Supplement_IsCliffordGate
open MeasureTheory

namespace PRUPermLayer.Supplement

/-- **Theorem 1.6** (mixed-access attack on one permutation between product layers;
Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Theorem 1.6, p.4 (PDF p.6); proof §8.2 and Appendix A, pp.26–28 (PDF pp.28–30)).
Let `n ≥ 2` and `N = 2ⁿ`. There is an algorithm, independent of the oracle, that makes two forward
and two inverse queries without controlled access and distinguishes every unitary `U = L₁PL₂`,
where `L₁, L₂` are single-qubit product unitaries and `P` is a permutation of the computational
basis, from a Haar-random unitary with advantage at least `1/36 − 3/N²`. A second such algorithm
achieves advantage at least `1/9 − 3/N²` for every such `U` whose layers `L₁` and `L₂` consist of
Clifford gates.

**Formalization Note** "Independent of the oracle": each algorithm is chosen before `U`
(`∃ alg, ∀ C₁ C₂ σ`). Algorithms are `MixAlg n 4` (any workspace, any final effect, oracle calls
`U ⊗ I` or `U† ⊗ I` only, so no controlled access), with exactly two forward and two inverse
queries in a fixed order. This is stronger than §2.2's general mixed-access model, where directions
may depend classically on earlier outcomes, and matches the fixed order of the exhibited attack.
`L₁ = layerUnitary C₁`, `L₂ = layerUnitary C₂` for arbitrary `C₁ C₂ : Fin n → U(2)`, and
`P = permUnitary σ` for an arbitrary permutation `σ` of the `N` basis labels; `U` is fixed (not
random). The advantage against `U` is `|Pr[A^U = 1] − E_{V∼Haar} Pr[A^V = 1]|`. A Clifford layer
has every factor a single-qubit Clifford gate (`IsCliffordGate`, global phases allowed).
`3/N²` is `3 / (2ⁿ)²`. The conjunct `Integrable (V ↦ Pr[A^V = 1]) Haar` (true for every algorithm: the
acceptance probability is continuous and bounded on the compact group) makes the Haar expectation a
genuine expectation, not the junk value `0`. -/
theorem theorem_1_6 (n : ℕ) (hn : 2 ≤ n) :
    (∃ alg : MixAlg n 4,
      (Finset.univ.filter fun i => alg.d i = true).card = 2 ∧
      (Finset.univ.filter fun i => alg.d i = false).card = 2 ∧
      Integrable (fun V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
        mixAcceptProb alg (V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (haar n) ∧
      ∀ (C₁ C₂ : Fin n → Matrix.unitaryGroup Bool ℂ) (σ : Equiv.Perm (Fin (2 ^ n))),
        1 / 36 - 3 / ((2 : ℝ) ^ n) ^ 2 ≤
          |mixAcceptProb alg
              ((layerUnitary C₁ * permUnitary σ * layerUnitary C₂ :
                Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
            ∫ V, mixAcceptProb alg (V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ∂(haar n)|) ∧
    (∃ alg : MixAlg n 4,
      (Finset.univ.filter fun i => alg.d i = true).card = 2 ∧
      (Finset.univ.filter fun i => alg.d i = false).card = 2 ∧
      Integrable (fun V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
        mixAcceptProb alg (V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) (haar n) ∧
      ∀ (C₁ C₂ : Fin n → Matrix.unitaryGroup Bool ℂ), (∀ k, IsCliffordGate (C₁ k)) →
        (∀ k, IsCliffordGate (C₂ k)) → ∀ σ : Equiv.Perm (Fin (2 ^ n)),
        1 / 9 - 3 / ((2 : ℝ) ^ n) ^ 2 ≤
          |mixAcceptProb alg
              ((layerUnitary C₁ * permUnitary σ * layerUnitary C₂ :
                Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
            ∫ V, mixAcceptProb alg (V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ∂(haar n)|) := by sorry

end PRUPermLayer.Supplement
