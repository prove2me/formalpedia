-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_E_7_active_spectrum_reduction
-- name    : SpectralFeedback.Supplement.theorem_E_7_active_spectrum_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:59:54.420131+00:00
-- url     : https://prove2.me/theorems/a0450c4b-f02d-4053-a5cc-0827895fa283
-- title:
--   Theorem E.7 — active-spectrum reduction: $G_{m,r}(\rho)=G_{m,r}(\rho_{[s]})$, $s=\min(d,mr)$
-- statement:
--   Let $\rho\succeq0$ act on $\mathbb C^d$, $1\le r\le d$ and $m\ge1$. Put $p=mr$, $s=\min(d,p)$, and in any decreasing spectral resolution of $\rho$ define
--
--   $$
--   \rho_{[s]}=\sum_{i=1}^s\lambda_i(\rho)e_ie_i^* .
--   $$
--
--   Then
--
--   $$
--   G_{m,r}(\rho)=G_{m,r}(\rho_{[s]}),\qquad\text{(E.12)}
--   $$
--
--   where the truncation is not renormalized. On $\rho_{[s]}$ the maximum is attained by $m$ atoms each of rank at most $r$, and adding $\rho-\rho_{[s]}$ to any one of these atoms attains the same optimum for $\rho$ with the same $m$ symbols.
--
--   This is the instance $F=\chi_r$ of the base mission's Lemma H.1. It needs the continuity and monotonicity of $\chi$, which the lemma takes as hypotheses.
--
--   Differences from the source:
--   - encoding: the value G_{m,r}(ρ) (a maximum, (C.6)) → IsGreatest of the published rewardSet with F = χ_r; reason: the base mission's convention; IsGreatest asserts the maximum exists and equals the value, never a junk sSup
--   - encoding: ρ_[s] in any decreasing spectral resolution → the published activePart ρ U (min d (m·r)) for every decreasing spectral basis U (IsSortedEigenbasis); reason: the statement holds for every such U
--   - reading: adding ρ − ρ_[s] to one of these atoms → to any atom h₀ of the rank-≤ r active optimizer; reason: 'one of these atoms' does not name the atom; the stronger reading (every choice works) is stated
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem E.7, (E.12), p.82 (PDF p.84)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_pairAtom
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem E.7** (Active-spectrum reduction; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.82 (PDF p.84)). Let `ρ ⪰ 0`
act on `ℂ^d`, let `1 ≤ r ≤ d`, and let `m ≥ 1`. Put `p = mr`, `s = min(d, p)`, and, in any
decreasing spectral resolution of `ρ`, define `ρ_{[s]} = ∑_{i=1}^s λ_i(ρ) e_i e_i*`. Then
`G_{m,r}(ρ) = G_{m,r}(ρ_{[s]})` (E.12). The truncation is not renormalized. On `ρ_{[s]}`, the maximum
can be attained with every atom of rank at most `r`. Adding `ρ − ρ_{[s]}` to one of these atoms
attains the same optimum for `ρ`, using at most the same `m` symbols.

**Formalization Note** `G_{m,r}(·) = v` is `IsGreatest (rewardSet r (chi r) m ·) v`; `ρ_{[s]}` is the
published `activePart ρ U (min d (m * r))` for an arbitrary decreasing spectral basis `U`
(`IsSortedEigenbasis`), and the statement holds for every such `U`. "One of these atoms" is read as
any atom `h₀` of the rank-`≤ r` active optimizer. -/
theorem theorem_E_7_active_spectrum_reduction (m r : ℕ) (hm : 1 ≤ m) {d : ℕ} (hr : 1 ≤ r)
    (hrd : r ≤ d) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : IsSortedEigenbasis ρ U) :
    ∃ v : ℝ,
      IsGreatest (rewardSet r (chi r) m ρ) v ∧
      IsGreatest (rewardSet r (chi r) m (activePart ρ U (min d (m * r)))) v ∧
      ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ h, (A h).PosSemidef) ∧
        ∑ h, A h = activePart ρ U (min d (m * r)) ∧ ∑ h, reward r (chi r) (A h) = v ∧
        (∀ h, (A h).rank ≤ r) ∧
        ∀ h₀ : Fin m,
          (∀ h, (Function.update A h₀ (A h₀ + (ρ - activePart ρ U (min d (m * r)))) h).PosSemidef) ∧
          ∑ h, Function.update A h₀ (A h₀ + (ρ - activePart ρ U (min d (m * r)))) h = ρ ∧
          ∑ h, reward r (chi r)
              (Function.update A h₀ (A h₀ + (ρ - activePart ρ U (min d (m * r)))) h) = v := by sorry

end Supplement

end SpectralFeedback
