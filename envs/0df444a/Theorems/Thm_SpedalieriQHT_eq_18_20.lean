-- Prove2me | Theorems.Thm_SpedalieriQHT_eq_18_20
-- name    : SpedalieriQHT.eq_18_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:32.601966+00:00
-- url     : https://prove2.me/theorems/0758b092-6734-41a6-bff8-0546592cb526
-- title:
--   Eqs. (18)–(20) — if one state is pure, the quantum Hoeffding bound is at most the fidelity bound, with equality for two pure states
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space of any dimension, $\psi_0\in\mathcal H$ a unit vector, $\rho_0=|\psi_0\rangle\langle\psi_0|$, and $r$ a real number. For states $\rho_0,\rho_1$ write $C_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and, for $\rho_0$ pure, $F=F(|\psi_0\rangle,\rho_1)=\langle\psi_0|\rho_1|\psi_0\rangle$,
--   $$
--   H(r)=\sup_{0\le s<1}\frac{-r s-\ln C_s}{1-s},\qquad H_F(r)=\sup_{0\le s<1}\frac{-r s-\ln F}{1-s}.
--   $$
--
--   1. **Fidelity bound, (18)–(19).** For every density operator $\rho_1$,
--   $$
--   H(r)\le H_F(r)\qquad\text{and}\qquad H_F(r)=\begin{cases}\ln\dfrac1F, & r\ge\ln\dfrac1F,\\[2mm]+\infty, & r<\ln\dfrac1F.\end{cases}
--   $$
--   2. **Tightness for two pure states, (20).** For every unit vector $\psi_1$ and $\rho_1=|\psi_1\rangle\langle\psi_1|$,
--   $$
--   H(r)=H_F(r).
--   $$
--   3. **The pure state in the other place, (18)–(19).** For every unit vector $\psi_1$, $\rho_1=|\psi_1\rangle\langle\psi_1|$ and every density operator $\rho_0$, with $F=\langle\psi_1|\rho_0|\psi_1\rangle$, the bound and the closed form of clause 1 hold.
--
--   Here $\ln 0=-\infty$, so orthogonal states ($F=0$) give $H_F(r)=+\infty$. The quantum Hoeffding bound is the optimal error exponent of false negatives in asymmetric quantum hypothesis testing under a constraint $r$ on the error exponent of false positives; the theorem bounds it through the fidelity alone whenever one of the states is pure, and evaluates it when both are.
--
--   **Formalization Note** Values in `EReal`; $\ln(1/F)$ is $-\operatorname{elog}F$.
--
--   Differences from the source:
--   - generalization: $r>0$ (Eq. (13)) → every real $r$; reason: (15)–(20) hold for every real $r$, and the statement specializes to $r>0$
--   - reading: $F(|\psi_0\rangle,\rho_1)$, "the fidelity between $|\psi_0\rangle$ and $\rho_1$" → $\langle\psi_0|\rho_1|\psi_0\rangle$; reason: the squared convention of Ref. [19] and of Eq. (21), $F(|\psi_0\rangle,|\psi_1\rangle)=|\langle\psi_0|\psi_1\rangle|^2$
--   - reading: one of the states pure, "e.g., $\rho_0=|\psi_0\rangle\langle\psi_0|$" → clause 1 (pure $\rho_0$) and clause 3 (pure $\rho_1$); reason: the section opens "when one of the states (or both) is pure" and $\rho_0$ is printed as an example, so the stronger reading is kept; the other placement is true ($C_s=\langle\psi|\rho^s|\psi\rangle\ge F$ on $0<s<1$, $C_0=1$) and is not a relabelling, since $C_s$ and $H(r)$ are not symmetric in $\rho_0,\rho_1$
--   - encoding: $\ln$, $\ln(1/F)$, $+\infty$, $\rho^s$, $\operatorname{Tr}$, states, pure states → `EReal` with $\ln 0=-\infty$ (`elog`) and $\ln(1/F)=-\operatorname{elog}F$, `CFC.rpow` powers ($\rho^0=I$, footnote [20]), real part of the basis-sum trace, density operators on an arbitrary complex Hilbert space (`IsDensityOp`), pure states `rankOne ℂ ψ ψ` with $\|\psi\|=1$; reason: Lean conventions; same instances
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eqs. (18)–(20), p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_SpedalieriQHT_pureState
import Definitions.Def_SpedalieriQHT_pureFidelity
import Definitions.Def_SpedalieriQHT_qhb
import Definitions.Def_SpedalieriQHT_fidelityBound

open HayashiHoeffding (elog IsDensityOp)

namespace SpedalieriQHT

/-- **Eqs. (18)–(20).** Let `ψ0` be a unit vector of a complex Hilbert space, `ρ0 = |ψ0⟩⟨ψ0|`,
and `r` real.
1. (Eqs. (18)–(19)) For every density operator `ρ1`, with `F = ⟨ψ0|ρ1|ψ0⟩`, the quantum
   Hoeffding bound satisfies `H(r) ≤ H_F(r)`, and `H_F(r) = ln(1/F)` for `r ≥ ln(1/F)`,
   `H_F(r) = +∞` for `r < ln(1/F)`.
2. (Eq. (20)) For every unit vector `ψ1`, with `ρ1 = |ψ1⟩⟨ψ1|`, the bound is tight:
   `H(r) = H_F(r)`.
3. (Eqs. (18)–(19), the pure state in the other place) For every unit vector `ψ1`, with
   `ρ1 = |ψ1⟩⟨ψ1|`, and every density operator `ρ0`, with `F = ⟨ψ1|ρ0|ψ1⟩`, the same bound and
   closed form hold.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, Eqs. (18)–(20), p.3: "Asymmetric testing
becomes very simple when one of the states (or both) is pure. … only one of the states is pure,
e.g., ρ0 = |ψ0⟩⟨ψ0| … we derive the
fidelity-bound H(r) ≤ H_F(r) := sup_{0≤s<1} (−r s − ln F)/(1 − s). (18) … After a simple
calculation we find H_F(r) = ln 1/F, for r ≥ ln 1/F ; +∞, for r < ln 1/F (19) … in the
discrimination of two pure states, we find that the previous fidelity-bound becomes tight
H(r) = H_F(r). (20)"

**Formalization Note.** `H(r)` is `qhb` (Eq. (15), a supremum in `EReal` over `0 ≤ s < 1` of
`(−r s − ln C_s)/(1 − s)`, `C_s = Tr(ρ0^s ρ1^{1−s})` with `CFC.rpow` powers, so `ρ^0 = 1`);
`H_F(r)` is `fidelityBound` (the supremum (18)); `ln(1/F)` is `-elog F`, `+∞` at `F = 0`. The
fidelity is the squared one, `⟨ψ|ρ|ψ⟩` for the pure `ψ` and the other state `ρ`. `r` is any real
number. The page's "e.g." is read as an example, so clause 3 states the case the page leaves to the
reader; `H(r)` is not symmetric in `ρ0, ρ1`, so it does not follow from clause 1 by relabelling. -/
theorem eq_18_20 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ0 : H) (hψ0 : ‖ψ0‖ = 1) (r : ℝ) :
    (∀ ρ1 : H →L[ℂ] H, IsDensityOp ρ1 →
      qhb (pureState ψ0) ρ1 r ≤ fidelityBound (pureFidelity ψ0 ρ1) r ∧
      fidelityBound (pureFidelity ψ0 ρ1) r =
        if -elog (pureFidelity ψ0 ρ1) ≤ (r : EReal) then -elog (pureFidelity ψ0 ρ1) else ⊤) ∧
    (∀ ψ1 : H, ‖ψ1‖ = 1 →
      qhb (pureState ψ0) (pureState ψ1) r =
        fidelityBound (pureFidelity ψ0 (pureState ψ1)) r) ∧
    (∀ ψ1 : H, ‖ψ1‖ = 1 → ∀ ρ0 : H →L[ℂ] H, IsDensityOp ρ0 →
      qhb ρ0 (pureState ψ1) r ≤ fidelityBound (pureFidelity ψ1 ρ0) r ∧
      fidelityBound (pureFidelity ψ1 ρ0) r =
        if -elog (pureFidelity ψ1 ρ0) ≤ (r : EReal) then -elog (pureFidelity ψ1 ρ0) else ⊤) := by sorry

end SpedalieriQHT
