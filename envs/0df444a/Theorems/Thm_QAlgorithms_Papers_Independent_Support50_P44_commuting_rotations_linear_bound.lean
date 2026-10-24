-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_commuting_rotations_linear_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P44.commuting_rotations_linear_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:38:31.814813+00:00
-- url     : https://prove2.me/theorems/00840165-ba3b-448c-9afa-6afced02ac36
-- title:
--   Commuting rotations give a state-dependent linear recovery bound
-- statement:
--   Let $\rho_{ABC}$ be a density operator on finite-dimensional complex systems $A,B,C$, with marginals $\rho_{BC}$, $\rho_B$ and $\rho_{AB}$. There exist a CPTP map $R:B\to B\otimes C$ and unitaries $U_B,V_{BC}$ commuting with $\rho_B,\rho_{BC}$ respectively, such that, for every $X$ supported on $\operatorname{supp}\rho_B$,
--
--   $$R(X)=V_{BC}\rho_{BC}^{1/2}(\rho_B^{-1/2}U_B XU_B^\dagger\rho_B^{-1/2}\otimes I_C)\rho_{BC}^{1/2}V_{BC}^\dagger,$$
--
--   and
--
--   $$F(\rho_{ABC},(\mathrm{id}_A\otimes R)(\rho_{AB}))\ge1-\frac{\ln2}{2}I(A:C\mid B)_\rho.$$
--
--   Inverse square roots are generalized inverses. The full CPTP map completes the supported formula outside that support, and may depend on the entire state. This is the nonuniversal structural recovery result used by the corollary.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 19, Lemma 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A B C E G : Type*}

/-- PDF pp.19–20, Lemma 6.1, (116)–(117). Source correction: the formula is
restricted to supported inputs as explicitly stipulated in (115); require a full
CPTP completion. Singular rhoB is allowed. R may depend on the full state. -/
theorem commuting_rotations_linear_bound [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hrho : IsDensityMatrix rho) :
    let rhoBC := traceLeft rho
    let rhoB : Matrix B B ℂ := fun b b2 => ∑ c, rhoBC (b,c) (b2,c)
    ∃ R : Superop B (B × C), IsChannel R ∧
      ∃ U : Matrix.unitaryGroup B ℂ, ∃ V : Matrix.unitaryGroup (B × C) ℂ,
        (U : Matrix B B ℂ) * rhoB = rhoB * (U : Matrix B B ℂ) ∧
        (V : Matrix (B × C) (B × C) ℂ) * rhoBC =
          rhoBC * (V : Matrix (B × C) (B × C) ℂ) ∧
        (∀ X, finiteSupport rhoB * X * finiteSupport rhoB = X →
          R X = rotatedTranspose rhoBC U V X) ∧
        1 - Real.log 2 / 2 * finiteCMI rho ≤
          rootFidelity rho (idTensorSuperop R (marginalAB rho)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
