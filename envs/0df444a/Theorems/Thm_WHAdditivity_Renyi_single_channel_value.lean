-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_single_channel_value
-- name    : WHAdditivity.Renyi.single_channel_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:53.842985+00:00
-- url     : https://prove2.me/theorems/6d6479c0-a470-4064-b49b-79558a99c597
-- title:
--   p. 3 — MEOₚ[Γ_d] = log(d − 1): every pure input gives (1/(d−1))(𝟙 − |φ̄⟩⟨φ̄|)
-- statement:
--   Let $d \ge 2$ and $p \ge 1$, and let $\Gamma_d$ be the Werner–Holevo channel $\Gamma_d(X) = \frac{1}{d-1}(\operatorname{Tr}(X)\,\mathbb 1 - X^{\mathsf T})$ on $d\times d$ complex matrices. For a unit vector $\varphi\in\mathbb C^d$ write $\bar\varphi$ for its entrywise complex conjugate. Then:
--
--   1. for every unit vector $\varphi$, $\Gamma_d(|\varphi\rangle\langle\varphi|) = \frac{1}{d-1}\bigl(\mathbb 1 - |\bar\varphi\rangle\langle\bar\varphi|\bigr)$;
--   2. for every unit vector $\varphi$, $S_p\bigl(\Gamma_d(|\varphi\rangle\langle\varphi|)\bigr) = \log(d-1)$;
--   3. the set of values $S_p(\Gamma_d(|\varphi\rangle\langle\varphi|))$, $\|\varphi\| = 1$, is bounded below, and
--   $$\mathrm{MEO}_p[\Gamma_d] = \inf_{\varphi,\ \|\varphi\|=1} S_p\bigl(\Gamma_d(|\varphi\rangle\langle\varphi|)\bigr) = \log(d-1).$$
--
--   Here $S_p$ is the $p$-Rényi entropy $-\frac{1}{p-1}\log\operatorname{Tr}\rho^p$ for $p > 1$ and the von Neumann entropy $S$ for $p = 1$, with the natural logarithm.
--
--   This is the single-channel value: every pure input is mapped to the same flat spectrum, so the right-hand side of the additivity formula (7) is $\sum_j \log(d_j - 1)$.
--
--   **Formalization Note.** $\bar\varphi$ is `star φ`; $|\varphi\rangle\langle\varphi|$ is `Matrix.vecMulVec φ (star φ)`; $\Gamma_d$ is the linear extension of (6) to all matrices.
--
--   Differences from the source:
--   - encoding: Γ_d defined for d ≥ 1 by (6), with 1/(d − 1) → hypothesis 2 ≤ d; reason: (6) divides by d − 1, so d = 1 is undefined in the paper and junk (0⁻¹ = 0) in Lean.
--   - encoding: Γ_d(ρ) = (1/(d−1))(𝟙 − ρᵀ) on density matrices → (Tr X · 𝟙 − Xᵀ)/(d − 1) on all matrices; reason: agrees with (6) on every trace-one input, in particular on |φ⟩⟨φ|.
--   - encoding: MEO_p at p = 1 defined as the limit p ↓ 1 → S_1 := S, the von Neumann entropy; reason: the paper extends the notation to p = 1 by this limit, whose value is S.
--   - encoding: MEO_p as an infimum → real `sInf`, with bounded-belowness of the set concluded; reason: Lean's `sInf` of a set unbounded below is 0; concluding the bound adds content and excludes the junk case.
--   - encoding: log unspecified → natural logarithm; reason: the paper's log has no stated base, and log(d − 1) on both sides fixes nothing else.
--   - generalization: the display states the chain of equal infima → Lean also asserts the two pointwise identities under the infimum, for every unit φ; reason: they imply the display (the infimum of a constant is that constant), and the middle line of the display is the first identity.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, p. 3, display after 'A straightforward computation yields'

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem single_channel_value (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    (∀ φ : Fin d → ℂ, IsUnitVector φ →
      wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ))) ∧
    (∀ φ : Fin d → ℂ, IsUnitVector φ →
      renyiEntropy p (wernerHolevo d (pureState φ)) = Real.log ((d : ℝ) - 1)) ∧
    BddBelow (outputEntropies p (wernerHolevo d)) ∧
    minOutputEntropy p (wernerHolevo d) = Real.log ((d : ℝ) - 1) := by sorry

end WHAdditivity.Renyi
