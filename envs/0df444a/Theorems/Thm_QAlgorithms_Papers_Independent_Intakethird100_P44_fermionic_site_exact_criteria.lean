-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P44_fermionic_site_exact_criteria
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P44.fermionic_site_exact_criteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:28:31.935142+00:00
-- url     : https://prove2.me/theorems/d795a491-32c1-4ba6-ac99-aaa8546179e2
-- title:
--   Exact strong-local correction for fermionic site regions
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, and every channel is completely positive and trace preserving on the full matrix algebra. Let $\omega$ be a set of fermionic sites, possibly empty, and $\mathcal A_\omega$ its even local CAR algebra on the full Fock space. Let $C_\omega$ be regional parity, $P_\pm=(I\pm C_\omega)/2$, and $\mathcal N(X)=\sum_iE_iXE_i^\dagger$ a normalized channel with $E_i\in\mathcal A_\omega$. Let $W$ be any isometric code. Strong locality means the adjoint preserves $\mathcal A_\omega$ and fixes its full ambient commutant $\mathcal A_\omega'$ pointwise. The target projection onto $\mathcal A_\omega\vee\mathcal A_\omega'$ is regional parity dephasing. Exact strong-local correction to this physical target is equivalent to each condition:
--
--   1. There are normalized environment densities $\rho_+,\rho_-$ such that for every $B\in\mathcal A_\omega'$ and environment matrix $X$,
--   $$
--   \sum_{ij}X_{ij}W^\dagger E_i^\dagger BE_jW=\sum_{s\in\{+,-\}}\operatorname{Tr}(\rho_sX)W^\dagger P_sBP_sW.
--   $$
--   2. One complex array $\lambda_{ijs}$, uniform in $B$, satisfies, with $B_s=P_sBP_s$,
--   $$
--   W^\dagger E_i^\dagger E_jB_sW=\lambda_{ijs}W^\dagger B_sW\quad\text{for all }i,j,s,\ B\in\mathcal A_\omega'.
--   $$
--
--   The $B_s$ commute with the noise operators. For $\omega=\varnothing$, $C_\omega=I$ and $P_-=0$; no nonzero-sector assumption is added.
-- source:
--   Approximate recovery with locality and symmetry constraints, arXiv:1806.10324v2, PDF p. 10, §IV E, Eqs.(53)–(54): exact strong local correction for fermionic site regions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P44

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P48 (operatorTraceDual)

open QAlgorithms.Papers.Independent.Renew46.P43 (purification)

variable {H K L J E F B : Type*}

variable [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype B] [DecidableEq B]

/-- PDF p.10, Eqs.(53)--(54): exact strong-local correction for fermionic
SITE regions. The empty region is allowed; its unused minus sector is zero. 
Parity correction, PDF p.2 Eq.(1): printed i^(|omega|-1) for Majorana labels;
changed to i^m on 2m ordered modes. Why: the printed four-mode value is
anti-Hermitian with square -I, whereas the source requires parity sectors of
a Hermitian involution. Only this normalization (up to sign) is corrected. -/
theorem fermionic_site_exact_criteria {n : ℕ} [Nonempty L] [Nonempty J]
    (f : Fermions n) (omega : Finset (Fin n))
    (noise : J → Mat (Fin (2 ^ n))) (hnoise : IsKrausFamily noise)
    (hlocal : ∀ i, noise i ∈ evenRegion f (siteModes omega))
    (W : Matrix (Fin (2 ^ n)) L ℂ) (hW : Wᴴ * W = 1) :
    (StrongCorrectable (evenRegion f (siteModes omega) : Set _) (regionParity f omega)
        (krausApply noise) W ↔
      RegionalStateCondition (evenRegion f (siteModes omega) : Set _)
        (regionParity f omega) noise W) ∧
    (StrongCorrectable (evenRegion f (siteModes omega) : Set _) (regionParity f omega)
        (krausApply noise) W ↔
      RegionalCoefficients (evenRegion f (siteModes omega) : Set _)
        (regionParity f omega) noise W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P44

end
