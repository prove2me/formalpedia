-- Prove2me | Theorems.Thm_SpedalieriQHT_footnote_20
-- name    : SpedalieriQHT.footnote_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:37.515866+00:00
-- url     : https://prove2.me/theorems/cf231a45-7581-4f5d-8080-ffe0c870bb9f
-- title:
--   Footnote [20] — for two pure states, $H(r)=\sup_{0<s<1}P(r,s)=\ln\frac1F$ or $+\infty$
-- statement:
--   Let $\psi_0,\psi_1$ be unit vectors of a complex Hilbert space, $\rho_0=|\psi_0\rangle\langle\psi_0|$, $\rho_1=|\psi_1\rangle\langle\psi_1|$, $F=F(|\psi_0\rangle,|\psi_1\rangle)$, and $r$ real. With $P(r,s)$ and $H(r)$ as in (15):
--
--   1. $H(r)=\max\bigl\{P(r,0),\ \sup_{0<s<1}P(r,s)\bigr\}$;
--   2. $P(r,0)=-\ln C_0=0$;
--   3. the term $P(r,0)$ can be neglected: $H(r)=\sup_{0<s<1}P(r,s)$;
--   4. $$\sup_{0<s<1}P(r,s)=\sup_{0<s<1}\frac{-r s-\ln F}{1-s}=\begin{cases}\ln\dfrac1F, & r\ge\ln\dfrac1F,\\[2mm]+\infty, & r<\ln\dfrac1F.\end{cases}$$
--
--   This is the computation behind the tightness (20) of the fidelity bound for two pure states.
--
--   **Formalization Note** Values in `EReal`; $\ln(1/F)$ is $-\operatorname{elog}F$ ($+\infty$ at $F=0$). Clause 2 rests on $\rho^0=I$.
--
--   Differences from the source:
--   - generalization: $r>0$ (Eq. (13)) → every real $r$; reason: the footnote's computation holds for every real $r$, and the statement specializes to $r>0$
--   - reading: $F$ the fidelity of the two pure states → $\langle\psi_0|\rho_1|\psi_0\rangle$; reason: the squared convention of Eq. (21), $F=|\langle\psi_0|\psi_1\rangle|^2$
--   - encoding: $\ln$, $\ln(1/F)$, $+\infty$, $\rho^s$, $\operatorname{Tr}$ → `EReal` with $\ln 0=-\infty$ and $\ln(1/F)=-\operatorname{elog}F$, `CFC.rpow` powers ($\rho^0=I$), real part of the basis-sum trace, pure states `rankOne ℂ ψ ψ` with $\|\psi\|=1$ on an arbitrary complex Hilbert space; reason: Lean conventions; same instances
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, footnote [20], p.8

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_SpedalieriQHT_pureState
import Definitions.Def_SpedalieriQHT_pureFidelity
import Definitions.Def_SpedalieriQHT_hoeffdingP
import Definitions.Def_SpedalieriQHT_qhb

open HayashiHoeffding (elog)

namespace SpedalieriQHT

/-- **Footnote [20].** For unit vectors `ψ0, ψ1`, every real `r`, `ρ0 = |ψ0⟩⟨ψ0|`,
`ρ1 = |ψ1⟩⟨ψ1|` and `F = F(|ψ0⟩, |ψ1⟩)`:
1. `H(r) = max{P(r, 0), sup_{0<s<1} P(r, s)}`;
2. `P(r, 0) = −ln C_0 = 0`;
3. this term can be neglected: `H(r) = sup_{0<s<1} P(r, s)`;
4. `sup_{0<s<1} P(r, s) = sup_{0<s<1} (−r s − ln F)/(1 − s)`, and this equals `ln(1/F)` for
   `r ≥ ln(1/F)` and `+∞` for `r < ln(1/F)`.

Spedalieri–Braunstein, arXiv:1407.0884v3, footnote [20], p.8: "We can write
H(r) = max{P(r, 0), sup_{0<s<1} P(r, s)}, where P(r, 0) = −ln C0 = 0 can be neglected and
sup_{0<s<1} P(r, s) = sup_{0<s<1} (−r s − ln F)/(1 − s) = ln 1/F for r ≥ ln 1/F, +∞ for
r < ln 1/F."

**Formalization Note.** Values in `EReal`; `ln(1/F)` is `-elog F` (`+∞` at `F = 0`). Clause 2
rests on `ρ^0 = 1` (`CFC.rpow`), so `C_0 = Tr ρ1 = 1`. -/
theorem footnote_20 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ0 ψ1 : H) (hψ0 : ‖ψ0‖ = 1) (hψ1 : ‖ψ1‖ = 1) (r : ℝ) :
    qhb (pureState ψ0) (pureState ψ1) r =
        max (hoeffdingP (pureState ψ0) (pureState ψ1) r 0)
          (⨆ s ∈ Set.Ioo (0 : ℝ) 1, hoeffdingP (pureState ψ0) (pureState ψ1) r s) ∧
      hoeffdingP (pureState ψ0) (pureState ψ1) r 0 = 0 ∧
      qhb (pureState ψ0) (pureState ψ1) r =
        ⨆ s ∈ Set.Ioo (0 : ℝ) 1, hoeffdingP (pureState ψ0) (pureState ψ1) r s ∧
      (⨆ s ∈ Set.Ioo (0 : ℝ) 1, hoeffdingP (pureState ψ0) (pureState ψ1) r s) =
        (⨆ s ∈ Set.Ioo (0 : ℝ) 1, (((-(r * s) : ℝ) : EReal) -
          elog (pureFidelity ψ0 (pureState ψ1))) / ((1 - s : ℝ) : EReal)) ∧
      (⨆ s ∈ Set.Ioo (0 : ℝ) 1, (((-(r * s) : ℝ) : EReal) -
          elog (pureFidelity ψ0 (pureState ψ1))) / ((1 - s : ℝ) : EReal)) =
        if -elog (pureFidelity ψ0 (pureState ψ1)) ≤ (r : EReal)
        then -elog (pureFidelity ψ0 (pureState ψ1)) else ⊤ := by sorry

end SpedalieriQHT
