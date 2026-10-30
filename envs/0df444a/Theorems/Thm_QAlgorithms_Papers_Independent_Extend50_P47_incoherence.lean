-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_incoherence
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.incoherence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:17:56.697722+00:00
-- url     : https://prove2.me/theorems/dc1168ec-a9ba-4f35-a8f9-d5bae8862104
-- title:
--   Remark 1: incoherence as cyclic-group symmetry
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For integer d≥1, cyclic Zd acting by Z(z)=Σj exp(2πijz/d)|j⟩⟨j|, the invariant densities are exactly the diagonal densities, equivalently the fixed points of complete dephasing. Algorithm 2 optimal acceptance is their maximum squared fidelity.
--
--   $$
--   \rho=Z(z)\rho Z(z)^\dagger\ (0\le z<d)\iff\rho=\sum_jp_j|j\rangle\langle j|,\quad p_j\ge0,\ \sum_jp_j=1.
--   $$
--
--   $Z(z)=\sum_{j=0}^{d-1}e^{2\pi i jz/d}|j\rangle\langle j|$; the comparison states for Algorithm 2 are exactly the diagonal densities.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 10, Remark 1: incoherence as cyclic-group symmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF pp.9–10, Remark 1: cyclic conjugation invariance is precisely diagonality. -/
theorem incoherence {d : ℕ} (hd : 0 < d) (rho : Mat (Fin d))
    (hrho : IsDensityMatrix rho)
    {Pur : Type*} [Fintype Pur] [DecidableEq Pur] [Nonempty Pur]
    (psi : EuclideanSpace ℂ (Pur × Fin d)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho) :
    (Sym (incoherentClock d) rho ↔
      ∃ p : Fin d → ℝ, (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
        rho = Matrix.diagonal (fun j => (p j : ℂ))) ∧
    (rho = (Fintype.card (Fin d) : ℂ)⁻¹ •
      ∑ z, incoherentClock d z * rho * (incoherentClock d z)ᴴ ↔
      ∀ i j, i ≠ j → rho i j = 0) ∧
    TestIdentity psi (symTest (incoherentClock d)) rho (Sym (incoherentClock d)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
