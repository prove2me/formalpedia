-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_A_1
-- name    : ShadowBootstrap.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:25.831538+00:00
-- url     : https://prove2.me/theorems/838b56e4-4e1e-4258-839e-c133429ed2de
-- title:
--   Lemma A.1 — variance constants of a product ensemble: $(C_A+1)(C_B+1)$
-- statement:
--   Let $E_A$ and $E_B$ be independent finite unitary ensembles on $n_A$ and $n_B$ qubits with invertible shadow channels. Suppose that for every state $\rho_A$ and Hermitian $O_A$ on $A$, and every state $\rho_B$ and Hermitian $O_B$ on $B$,
--   $$\mathrm{Var}\big[\operatorname{Tr}(O_A\hat\rho_A)\big] \le C_A\|O_A\|_F^2,\qquad \mathrm{Var}\big[\operatorname{Tr}(O_B\hat\rho_B)\big] \le C_B\|O_B\|_F^2 .$$
--   Then the shadow channel of $E_A \otimes E_B$ is invertible and, for every joint state $\rho_{AB}$ and Hermitian $O_{AB}$, its matched shadow estimator satisfies
--   $$\mathrm{Var}\big[\operatorname{Tr}(O_{AB}\hat\rho_{AB})\big] \le (C_A+1)(C_B+1)\|O_{AB}\|_F^2 .$$
--
--   It extends the two-layer bound to the suffix ensembles $E_{2L}(km)\otimes\mathrm{Cl}(r)$ of Lemma A.2.
--
--   Differences from the source:
--   - generalization: (conclusion) the variance bound → also: the shadow channel of E_A ⊗ E_B is invertible; reason: the matched shadow estimator presupposes it; the proof's M_AB = M_A ⊗ M_B gives it
--   - encoding: ensembles on registers A and B → finite ensembles; E_A on the first n_A qubits of the joint register; reason: the same product ensemble
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma A.1, p.33 (extension of [COK26, Lemma 25])

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_tensorEnsemble

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma A.1, p.33 (extension of [COK26, Lemma 25]): let `E_A`, `E_B` be independent unitary
ensembles on `n_A` and `n_B` qubits with invertible shadow channels such that, for every state and
Hermitian observable, `Var[Tr(O_A ρ̂_A)] ≤ C_A‖O_A‖_F²` and `Var[Tr(O_B ρ̂_B)] ≤ C_B‖O_B‖_F²`. Then for
every joint state `ρ_AB` and Hermitian observable `O_AB` the matched shadow estimator of
`E_A ⊗ E_B` satisfies `Var[Tr(O_AB ρ̂_AB)] ≤ (C_A + 1)(C_B + 1)‖O_AB‖_F²`.

**Formalization Note** The ensembles are arbitrary finite unitary ensembles (not necessarily
Clifford). `E_A` acts on the first `n_A` qubits of the joint register. The statement also asserts
that the shadow channel of `E_A ⊗ E_B` is invertible, which its matched shadow estimator
presupposes. -/
theorem lemma_A_1 {a b : ℕ} {ιA ιB : Type} [Fintype ιA] [Fintype ιB] (EA : Primitive a ιA)
    (EB : Primitive b ιB) (hA : IsUnit (measChannel EA)) (hB : IsUnit (measChannel EB))
    (CA CB : ℝ)
    (hvarA : ∀ ρ : Op a, WildeQIT.IsDensityOperator ρ → ∀ O : Op a, O.IsHermitian →
      snapVar EA ρ O ≤ CA * frobSq O)
    (hvarB : ∀ ρ : Op b, WildeQIT.IsDensityOperator ρ → ∀ O : Op b, O.IsHermitian →
      snapVar EB ρ O ≤ CB * frobSq O) :
    IsUnit (measChannel (tensorEnsemble EA EB)) ∧
      ∀ ρ : Op (a + b), WildeQIT.IsDensityOperator ρ → ∀ O : Op (a + b), O.IsHermitian →
        snapVar (tensorEnsemble EA EB) ρ O ≤ (CA + 1) * (CB + 1) * frobSq O := by sorry

end ShadowBootstrap
