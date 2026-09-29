-- Prove2me | Theorems.Thm_StochasticProg_IntegerLShaped_prop1_cuts_valid_for_sip
-- name    : StochasticProg.IntegerLShaped.prop1_cuts_valid_for_sip
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:12:39.848991+00:00
-- url     : https://prove2.me/theorems/bd1bd7c6-3c74-4fc1-9709-7a8757c4a5a0
-- title:
--   Chapter 7, Proposition 1 — L-shaped cuts on the continuous relaxation are valid for the SIP
-- statement:
--   The book's Chapter 7, Proposition 1 (p. 290) is stated for $C(x)$, the value of the
--   recourse problem relaxed over $\overline Y$, the continuous/LP-relaxation of $Y$ — which
--   can retain bounds $Y$ imposes beyond integrality (e.g. binary $Y=\{0,1\}^{m_2}$ gives
--   $\overline Y=[0,e]$, not $y\ge0$ alone). This mission formalizes $C(x)$ as the value
--   obtained by dropping $Y$ *entirely* (only $y \ge 0$ imposed), which coincides with the
--   book's $\overline Y$-based $C(x)$ only when $Y$ is itself an unbounded integrality
--   restriction; call this narrower quantity $C_0(x)$ below, and let $Q(x)$ denote the true,
--   $Y$-restricted recourse value of the stochastic integer program.
--
--   **Chapter 7, Proposition 1, as mechanized.** L-shaped optimality cuts of the form
--   $e - E^{\mathsf T}x \le C_0(x)$, computed on this dropped-$Y$ relaxation, remain valid —
--   i.e. $e - E^{\mathsf T}x \le Q(x)$ — as cuts for the SIP. When $Y$ is an unbounded
--   integrality restriction, $C_0(x) = C(x)$ and this is exactly the book's Proposition 1;
--   for a $Y$ that also imposes bounds (as in the book's own binary example), $C_0(x)$ can
--   be strictly *below* the book's $\overline Y$-based $C(x)$, so `hcut` here is a
--   *stronger*, narrower hypothesis than the book's own "the cut is valid for $C(x)$" — the
--   conclusion is unaffected because $C_0(x) \le C(x) \le Q(x)$ regardless.
--
--   This is immediate from $C_0(x) \le Q(x)$: restricting the recourse variable to $Y$ can
--   only raise (or leave unchanged) the minimal second-stage cost, since every $Y$-feasible
--   $y$ is also feasible for the dropped-$Y$ relaxation.
--
--   **Formalization Note** The premise "the cut is valid for $C_0(x)$" is taken as an
--   explicit hypothesis (`hcut`) rather than re-derived, since $C_0$ coincides with the
--   continuous relaxation `Recourse.Q d.toInstance` already established by the (continuous)
--   L-shaped method's own optimality-cut validity, established in the
--   Chapter 5 mission of this series.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 290, Chapter 7, Proposition 1

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 7, Proposition 1 (p. 290): "L-shaped optimality cuts of the form (5.1.4)
calculated on the continuous relaxation (1.3)-(1.4) are valid cuts for (SIP)."

**Formalization Note (scope, revised 2026-09-19 per moderator review).**
`Recourse.Q d.toInstance x` is *not* in general the book's `C(x)` of Eq. (1.3)-(1.4):
`d.toInstance` drops the restriction `Y` entirely, leaving only `y ≥ 0`, whereas the
book's `C(x)` is computed over `Ȳ`, the continuous/LP-relaxation of `Y` — which the
book's own worked example on this same page shows can be strictly smaller than
`{y ≥ 0}` (binary `Y = {0,1}^{m2}` gives `Ȳ = [0,e]`, not `y ≥ 0`). The two coincide only
when `Y` is itself an unbounded integrality restriction. This theorem is nonetheless
mathematically true as stated: `Q d.toInstance x ≤ QY d x` holds unconditionally, by
feasible-set monotonicity (every `Y`-feasible `y` is `{y ≥ 0}`-feasible), so a cut valid
for `d.toInstance`'s value transfers to `QY` regardless of what `Y` is — but it is a
**narrower** result than the book's Proposition 1 whenever `Y` carries structure beyond
unbounded integrality, since the hypothesis `hcut` then concerns a possibly-looser bound
than the book's own `C(x)`. A cut `e − Eᵀx ≤ C(x)` established for the continuous
relaxation (by the L-shaped method of Chapter 5, cited here as the hypothesis `hcut`,
since that is where the cut's coefficients `(E, e)` are shown valid) therefore also
lower-bounds the true, `Y`-restricted recourse value `Q(x)`, provided `hcut`'s own `Q
d.toInstance x` is read as this mission's (possibly narrower) relaxation rather than the
book's general `Ȳ`-based `C(x)`. -/
theorem prop1_cuts_valid_for_sip (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ)
    (E : Fin n1 → ℝ) (e : ℝ)
    (hcut : (e : EReal) - ((dotProduct E x : ℝ) : EReal) ≤ Q d.toInstance x) :
    (e : EReal) - ((dotProduct E x : ℝ) : EReal) ≤ QY d x := by sorry

end StochasticProg.IntegerLShaped
