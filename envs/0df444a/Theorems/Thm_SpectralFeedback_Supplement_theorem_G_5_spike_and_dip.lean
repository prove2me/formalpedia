-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_G_5_spike_and_dip
-- name    : SpectralFeedback.Supplement.theorem_G_5_spike_and_dip
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:01:46.481995+00:00
-- url     : https://prove2.me/theorems/c4d85ed4-82f3-4fd8-a5b4-3004b9323962
-- title:
--   Theorem G.5 — one spike and one dip, with the tail pooled into one existing symbol
-- statement:
--   Let $m,s\ge2$ and $p=ms$ (standing in §G.2). Suppose the active spectrum of $\rho\succeq0$ (its leading $p$ eigenvalues, padded with zeros and not renormalized) is
--
--   $$
--   (b+a,\ \underbrace{b,\dots,b}_{p-2},\ b-c),\qquad a\ge0,\quad 0\le c\le b.
--   $$
--
--   Then
--
--   $$
--   G_{m,s}(\rho)=\chi_s(mb+a-c,\ \underbrace{mb,\dots,mb}_{s-1}).
--   $$
--
--   Eigenvalues outside the active space are pooled into one existing coarse symbol: for every decreasing spectral basis there is an optimal $m$-atom decomposition of the active matrix $\rho_{[\min(d,p)]}$ such that adding $\rho-\rho_{[\min(d,p)]}$ to any one of its atoms gives an optimal decomposition of $\rho$ with the same $m$ atoms.
--
--   This is the appendix form of Theorem 7.1. It holds for subnormalized $\rho$ and adds the completion clause.
--
--   Differences from the source:
--   - encoding: the value G_{m,s}(ρ) → IsGreatest of the published rewardSet with F = χ_s; reason: the base mission's convention
--   - encoding: the (unnormalized) active spectrum λ_1, …, λ_p, zero-padded → eigDesc ρ i for i < p (0-based); reason: the published eigDesc pads with zeros beyond d; same numbers
--   - reading: eigenvalues outside the active space are pooled into one existing coarse symbol → for every U, ∃ optimal active decomposition such that adding ρ − activePart ρ U (min d (m·s)) to any atom h₀ is optimal for ρ; reason: the sentence names no atom; the stronger reading (every choice works) is stated
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem G.5, p.102 (PDF p.104); standing assumptions §G.2, p.102

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_pairAtom
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem G.5** (One spike and one dip; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.102 (PDF p.104)). Standing
(§G.2): `p = ms` with `m ≥ 2`, `s ≥ 2`; the active spectrum is padded with zeros and not renormalized.
Suppose the active spectrum of `ρ` is `(b + a, b, …, b, b − c)` (`p − 2` middle entries), `a ≥ 0`,
`0 ≤ c ≤ b`. Then `G_{m,s}(ρ) = χ_s(mb + a − c, mb, …, mb)` (`s − 1` entries `mb`). Eigenvalues
outside the active space are pooled into one existing coarse symbol.

**Formalization Note** `G_{m,s}(·) = v` is `IsGreatest (rewardSet s (chi s) m ·) v`; `ρ` is any
complex positive semidefinite matrix. The active spectrum is `eigDesc ρ i`, `i < p` (0-based,
zero-padded). The pooling sentence is: for every decreasing spectral basis `U`, there is an optimal
`m`-atom decomposition of the active matrix `ρ_{[min(d,p)]}` (`activePart ρ U (min d (m * s))`)
such that adding the outside eigenvalues `ρ − ρ_{[min(d,p)]}` to any one of its atoms gives an
optimal decomposition of `ρ` with the same `m` atoms. -/
theorem theorem_G_5_spike_and_dip (m s : ℕ) (hm : 2 ≤ m) (hs : 2 ≤ s) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcb : c ≤ b)
    (hspec : eigDesc ρ 0 = b + a ∧ (∀ i, 1 ≤ i → i ≤ m * s - 2 → eigDesc ρ i = b) ∧
      eigDesc ρ (m * s - 1) = b - c) :
    IsGreatest (rewardSet s (chi s) m ρ)
        (chi s (fun i => if (i : ℕ) = 0 then (m : ℝ) * b + a - c else (m : ℝ) * b)) ∧
      ∀ U : Matrix (Fin d) (Fin d) ℂ, IsSortedEigenbasis ρ U →
        ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ h, (A h).PosSemidef) ∧
          ∑ h, A h = activePart ρ U (min d (m * s)) ∧
          ∑ h, reward s (chi s) (A h) =
            chi s (fun i => if (i : ℕ) = 0 then (m : ℝ) * b + a - c else (m : ℝ) * b) ∧
          ∀ h₀ : Fin m,
            (∀ h, (Function.update A h₀ (A h₀ + (ρ - activePart ρ U (min d (m * s)))) h).PosSemidef) ∧
            ∑ h, Function.update A h₀ (A h₀ + (ρ - activePart ρ U (min d (m * s)))) h = ρ ∧
            ∑ h, reward s (chi s)
                (Function.update A h₀ (A h₀ + (ρ - activePart ρ U (min d (m * s)))) h) =
              chi s (fun i => if (i : ℕ) = 0 then (m : ℝ) * b + a - c else (m : ℝ) * b) := by sorry

end Supplement

end SpectralFeedback
