-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_G_2_flat_active_band
-- name    : SpectralFeedback.Supplement.theorem_G_2_flat_active_band
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:00:58.749052+00:00
-- url     : https://prove2.me/theorems/3d74ac9b-5f26-418b-9f21-2adf35e9b259
-- title:
--   Theorem G.2 — flat active band: spike branch (G.1) and dip branch (G.2)
-- statement:
--   Let $\rho\succeq0$, $m\ge2$, $s\ge1$ and $p=ms$. Let $\lambda_1\ge\dots\ge\lambda_p\ge0$ be the leading spectrum of $\rho$, with zeros appended if $p>\dim\rho$; the discarded tail is not included.
--
--   1. **Spike branch.** If $\lambda_{s+1}=\dots=\lambda_p=b$, then
--   $$
--   G_{m,s}(\rho)=\chi_s\bigl(\lambda_1+(m-1)b,\dots,\lambda_s+(m-1)b\bigr).\qquad\text{(G.1)}
--   $$
--   2. **Dip branch.** If $\lambda_1=\dots=\lambda_{p-s}=a$, then
--   $$
--   G_{m,s}(\rho)=\chi_s\bigl((m-1)a+\lambda_{p-s+1},\dots,(m-1)a+\lambda_p\bigr).\qquad\text{(G.2)}
--   $$
--
--   In each branch, on the active space there are $m$ attaining atoms of rank at most $s$ with identical spectra: they are positive semidefinite, sum to the active matrix $\rho_{[\min(d,p)]}$, and their total reward is the displayed value. The formulas include zero bases, zero dips, repeated exceptional eigenvalues and zero padding.
--
--   Differences from the source:
--   - encoding: the value G_{m,s}(ρ) → IsGreatest of the published rewardSet with F = χ_s; reason: the base mission's convention
--   - encoding: the (unnormalized) active spectrum λ_1, …, λ_p, zero-padded → eigDesc ρ i for i < p (0-based); reason: the published eigDesc pads with zeros beyond d; same numbers
--   - encoding: attaining rank-at-most-s atoms with identical spectra on the active space → for every decreasing spectral basis U, m PSD atoms of rank ≤ s summing to activePart ρ U (min d (m·s)), with total reward the value and equal eigDesc lists; reason: the active space is the range of the published activePart; identical spectra means equal decreasing eigenvalue lists
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem G.2, (G.1)–(G.2), p.97 (PDF p.99)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_pairAtom
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem G.2** (Flat active band, arbitrary messages; Qi, *Spectral Structure and Exact
Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.97 (PDF p.99)).
Let `ρ ⪰ 0`, `m ≥ 2`, `s ≥ 1`, and put `p = ms`. Let `λ_1 ≥ ⋯ ≥ λ_p ≥ 0` be the leading spectrum of
`ρ`, with zeros appended if `p > dim ρ`. If `λ_{s+1} = ⋯ = λ_p = b`, then
`G_{m,s}(ρ) = χ_s(λ_1 + (m − 1)b, …, λ_s + (m − 1)b)` (G.1). If `λ_1 = ⋯ = λ_{p−s} = a`, then
`G_{m,s}(ρ) = χ_s((m − 1)a + λ_{p−s+1}, …, (m − 1)a + λ_p)` (G.2). On the active space there are
attaining rank-at-most-`s` atoms with identical spectra.

**Formalization Note** `G_{m,s}(·) = v` is `IsGreatest (rewardSet s (chi s) m ·) v`; `ρ` is any complex
positive semidefinite matrix (subnormalized allowed, §G.1.1). 0-based: `λ_i = eigDesc ρ (i − 1)`,
zero-padded. The active space carries `ρ_{[min(d,p)]}`, the published `activePart ρ U (min d (m * s))`
for any decreasing spectral basis `U`; "attaining atoms" are `m` positive semidefinite atoms of rank
`≤ s` summing to it with total reward the value of (G.1) resp. (G.2); "identical spectra" is equality
of all their decreasing eigenvalue lists. -/
theorem theorem_G_2_flat_active_band (m s : ℕ) (hm : 2 ≤ m) (hs : 1 ≤ s) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    (∀ b : ℝ, (∀ i, s ≤ i → i < m * s → eigDesc ρ i = b) →
      IsGreatest (rewardSet s (chi s) m ρ)
          (chi s (fun i => eigDesc ρ (i : ℕ) + ((m : ℝ) - 1) * b)) ∧
        ∀ U : Matrix (Fin d) (Fin d) ℂ, IsSortedEigenbasis ρ U →
          ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ h, (A h).PosSemidef) ∧
            ∑ h, A h = activePart ρ U (min d (m * s)) ∧
            ∑ h, reward s (chi s) (A h) = chi s (fun i => eigDesc ρ (i : ℕ) + ((m : ℝ) - 1) * b) ∧
            (∀ h, (A h).rank ≤ s) ∧ ∀ h h' i, eigDesc (A h) i = eigDesc (A h') i) ∧
    (∀ a : ℝ, (∀ i, i < m * s - s → eigDesc ρ i = a) →
      IsGreatest (rewardSet s (chi s) m ρ)
          (chi s (fun i => ((m : ℝ) - 1) * a + eigDesc ρ (m * s - s + (i : ℕ)))) ∧
        ∀ U : Matrix (Fin d) (Fin d) ℂ, IsSortedEigenbasis ρ U →
          ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ h, (A h).PosSemidef) ∧
            ∑ h, A h = activePart ρ U (min d (m * s)) ∧
            ∑ h, reward s (chi s) (A h) =
              chi s (fun i => ((m : ℝ) - 1) * a + eigDesc ρ (m * s - s + (i : ℕ))) ∧
            (∀ h, (A h).rank ≤ s) ∧ ∀ h h' i, eigDesc (A h) i = eigDesc (A h') i) := by sorry

end Supplement

end SpectralFeedback
