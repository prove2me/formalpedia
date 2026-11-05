-- Prove2me | Theorems.Thm_SpedalieriQHT_eq_17
-- name    : SpedalieriQHT.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:58.823192+00:00
-- url     : https://prove2.me/theorems/6a549767-ff6b-4723-b73c-a006130c6ec1
-- title:
--   Eq. (17) — if one state is pure, $\inf_s C_s=F(|\psi\rangle,\rho)$
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space, $\psi\in\mathcal H$ a unit vector, and $\rho$ a density operator on $\mathcal H$. Let $C_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$ be the s-overlap of two states $\rho_0,\rho_1$ and $F=F(|\psi\rangle,\rho)=\langle\psi|\rho|\psi\rangle$ the fidelity. If one of the two states is pure, that is, if $(\rho_0,\rho_1)=(|\psi\rangle\langle\psi|,\rho)$ or $(\rho_0,\rho_1)=(\rho,|\psi\rangle\langle\psi|)$, then
--   $$
--   \inf_{0\le s<1}C_s=F(|\psi\rangle,\rho);
--   $$
--   that is, $C_s\ge F$ for every $s\in[0,1)$, and $F$ is the greatest such lower bound.
--
--   The inequality $C_s\ge F$ is what turns the quantum Hoeffding bound (15) into the fidelity bound (18).
--
--   **Formalization Note** The infimum is stated as `IsGLB` of the image of $[0,1)$; it need not be attained.
--
--   Differences from the source:
--   - reading: $\inf_s C_s$, range of $s$ not printed → $s\in[0,1)$; reason: the range of (15), where the consequence $C_s\ge F$ is used to derive (18)
--   - reading: $F$ "the fidelity between $|\psi_0\rangle$ and $\rho_1$" → $\langle\psi_0|\rho_1|\psi_0\rangle$; reason: the squared convention of Ref. [19] and of Eq. (21), $F(|\psi_0\rangle,|\psi_1\rangle)=|\langle\psi_0|\psi_1\rangle|^2$
--   - reading: one of the states pure, "e.g., $\rho_0=|\psi_0\rangle\langle\psi_0|$" → both placements, $(\rho_0,\rho_1)=(|\psi\rangle\langle\psi|,\rho)$ and $(\rho,|\psi\rangle\langle\psi|)$; reason: the section opens "when one of the states (or both) is pure" and $\rho_0$ is printed as an example, so the stronger reading is kept; the other placement is true ($C_s=\langle\psi|\rho^s|\psi\rangle\ge F$ on $0<s<1$, $C_0=1$) and is not a relabelling, since $C_s$ and $H(r)$ are not symmetric in $\rho_0,\rho_1$
--   - encoding: states on an unspecified Hilbert space, $\rho^s$, $\operatorname{Tr}$, $\inf$ → density operators on an arbitrary complex Hilbert space (`IsDensityOp`), pure states `rankOne ℂ ψ ψ` with $\|\psi\|=1$, `CFC.rpow` powers ($\rho^0=I$), real part of the basis-sum trace, `IsGLB`; reason: Lean conventions; same instances
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eq. (17), p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_SpedalieriQHT_pureState
import Definitions.Def_SpedalieriQHT_pureFidelity
import Definitions.Def_SpedalieriQHT_sOverlap

open HayashiHoeffding (IsDensityOp)

namespace SpedalieriQHT

/-- **Eq. (17).** Let `‖ψ‖ = 1` and let `ρ` be a density operator. If one of the two states is the
pure state `|ψ⟩⟨ψ|` and the other is `ρ`, the infimum of the s-overlap `C_s = Tr(ρ0^s ρ1^{1−s})`
over `0 ≤ s < 1` is the fidelity `F(|ψ⟩, ρ) = ⟨ψ|ρ|ψ⟩`; in particular `C_s ≥ F` for every such `s`.
The first conjunct is the page's case `ρ0 = |ψ⟩⟨ψ|`, `ρ1 = ρ`; the second is `ρ0 = ρ`,
`ρ1 = |ψ⟩⟨ψ|`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, Eq. (17), p.3: "Asymmetric testing becomes very
simple when one of the states (or both) is pure. … Let us start by considering the case where only
one of the states is pure, e.g., ρ0 = |ψ0⟩⟨ψ0|. We can write [19] inf_s C_s = F(|ψ0⟩, ρ1), where F
is the fidelity between |ψ0⟩ and ρ1. Eq. (17) implies C_s ≥ F."

**Formalization Note.** The range of `s` in "inf_s" is not printed; it is the range
`0 ≤ s < 1` of (15), where the inequality `C_s ≥ F` is used. `IsGLB` states both that `F` is a
lower bound and that it is the greatest one (the infimum need not be attained). The fidelity is
the squared one, `⟨ψ|ρ|ψ⟩`, as in (21). Powers are `CFC.rpow` (`ρ^0 = 1`). The page's "e.g." is
read as an example, so both placements of the pure state are stated: `C_s` is not symmetric in
`ρ0, ρ1`, and for `ρ1` pure the infimum is approached as `s → 1⁻` instead of `s → 0⁺`. -/
theorem eq_17 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : H) (hψ : ‖ψ‖ = 1) (ρ : H →L[ℂ] H) (hρ : IsDensityOp ρ) :
    IsGLB ((fun s => sOverlap (pureState ψ) ρ s) '' Set.Ico (0 : ℝ) 1) (pureFidelity ψ ρ) ∧
      IsGLB ((fun s => sOverlap ρ (pureState ψ) s) '' Set.Ico (0 : ℝ) 1)
        (pureFidelity ψ ρ) := by sorry

end SpedalieriQHT
