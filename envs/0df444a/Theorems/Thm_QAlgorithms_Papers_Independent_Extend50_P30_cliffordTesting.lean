-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_cliffordTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.cliffordTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:59:20.879843+00:00
-- url     : https://prove2.me/theorems/95ff5443-891c-45fa-b27f-1e79cba99e6b
-- title:
--   Clifford testing via Choi states
-- statement:
--   For a unitary $U$ on $n$ qubits, let $|U\rangle=(U\otimes I)|\Phi^+\rangle$ be its normalized Choi state. This state is a stabilizer exactly when $U$ is Clifford. Its pure-state trace distance from $|V\rangle$ equals $D(U,V)=\sqrt{1-|2^{-n}\operatorname{tr}(U^\dagger V)|^2}$. Preparing six Choi states and running Algorithm 1 gives a perfectly complete test using $U$ alone. There exists a function $\eta(\varepsilon)>0$, independent of $n$, such that a unitary at distance at least $\varepsilon\in(0,1]$ from every Clifford is accepted with probability at most $1-\eta(\varepsilon)$. The anti-identity verification factors into $2n$ fixed-size local blocks, supplying efficient implementation.
--
--   $$
--   |U\rangle\text{ is stabilizer}\iff U\in\mathrm{Cliff}(n,2),\qquad p_{\rm accept}(U)\leq1-\eta(\varepsilon).
--   $$
--
--   This gives the source's clifford testing via choi states in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 22, remark-3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Remark 3.7: exact Choi characterization and dimension-independent unitary soundness.
The concrete tester prepares six Choi vectors using U alone, then applies Algorithm 1.
No numerical Clifford-distance constant is substituted for the source's qualitative guarantee. -/
theorem cliffordTesting :
    (∀ n : ℕ, QAlgorithms.IsEffect (qubitTest (n + n)) ∧
      ∀ U : QuditOperator 2 n, IsClifford U →
        QAlgorithms.effectProb (qubitTest (n + n))
          (tensorPower 6 (QAlgorithms.pureDensity (unitaryChoiVector n U))) = 1) ∧
    (∀ n : ℕ, ∀ U : QuditOperator 2 n, U ∈ Matrix.unitaryGroup (ResidueRegister 2 n) ℂ →
      (IsStabilizer (unitaryChoiVector n U) ↔ IsClifford U)) ∧
    (∀ n : ℕ, ∀ U V : QuditOperator 2 n,
      U ∈ Matrix.unitaryGroup (ResidueRegister 2 n) ℂ → V ∈ Matrix.unitaryGroup (ResidueRegister 2 n) ℂ →
      QAlgorithms.traceNorm (QAlgorithms.pureDensity (unitaryChoiVector n U) -
        QAlgorithms.pureDensity (unitaryChoiVector n V)) / 2 = unitaryDistance U V) ∧
    (∃ eta : ℝ → ℝ, ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      0 < eta epsilon ∧ ∀ n : ℕ, ∀ U : QuditOperator 2 n,
        U ∈ Matrix.unitaryGroup (ResidueRegister 2 n) ℂ →
        (∀ C : QuditOperator 2 n, IsClifford C → epsilon ≤ unitaryDistance U C) →
        QAlgorithms.effectProb (qubitTest (n + n))
          (tensorPower 6 (QAlgorithms.pureDensity (unitaryChoiVector n U))) ≤ 1 - eta epsilon) ∧
    (∀ m : ℕ, quditInvolution 2 m 3 =
      (List.ofFn (fun j : Fin m => embeddedLocal j (quditInvolution 2 1 3))).prod) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
