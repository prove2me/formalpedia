-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_theorem_C_19
-- name    : ProcessingNetworks.CTMCFoster.theorem_C_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:46.154522+00:00
-- url     : https://prove2.me/theorems/82e9b166-abbb-419e-9034-83232017f467
-- title:
--   Theorem C.19 — positive recurrence and stationary distributions of an irreducible discrete-time chain
-- statement:
--   Let $X$ be an irreducible discrete-time Markov chain on a countable state space $\mathscr S$ with transition matrix $P$, and write $m_i=\mathbb E_i(\tau_i)$ for the mean return time to $i$. The following are equivalent:
--
--   1. there is a state $\ell$ that is positive recurrent;
--   2. every state is positive recurrent;
--   3. the chain has a stationary distribution.
--
--   When any of these holds, the stationary distribution $\pi$ is unique and is given by
--
--   $$
--   \pi(i)=\frac1{m_i},\qquad i\in\mathscr S.
--   $$
--
--   This is the discrete-time classification result on which the Foster–Lyapunov criteria rest: it turns a drift bound on return times into existence and uniqueness of an equilibrium.
--
--   Differences from the source:
--   - encoding: the state space is nonempty by convention → `[Nonempty S]`; reason: on an empty type statement (b) would hold vacuously while (c) fails
--   - encoding: state $i$ recurrent with $m_i=\mathbb E_i(\tau_i)<\infty$ → `meanReturn P {i} i < ⊤`; reason: `meanReturn` is the tail sum $\sum_n\mathbb P_i(\tau_i>n)$ in $[0,\infty]$, which is infinite when return fails with positive probability
--   - encoding: "when any one of the above conditions is satisfied" → a universal statement over stationary distributions $\pi$; reason: the three conditions are equivalent, and (c) provides the $\pi$
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem C.19, eq. (C.11), p.279 (PDF 295)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_ProcessingNetworks_CTMCFoster_IsStationaryChain

namespace ProcessingNetworks.CTMCFoster

open KellyStochasticNetworks.MaxWeight
open scoped ENNReal

/-- Theorem C.19. For an irreducible discrete-time Markov chain on a countable state space the
following are equivalent: (a) some state `ℓ` is positive recurrent; (b) every state is positive
recurrent; (c) the chain has a stationary distribution. When they hold, the stationary distribution
is unique and `π(i) = 1 / m_i` (C.11), where `m_i = E_i(τ_i)`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem C.19,
eq. (C.11), p.279 (PDF 295).

**Formalization Note** `meanReturn P {i} i` is `m_i`, computed by the tail sum `∑ₙ P_i(τ_i > n)`
in `ℝ≥0∞`, so non-return counts as an infinite mean and `meanReturn P {i} i < ⊤` is "recurrent with
`m_i < ∞`" of Definition C.16. Since (a), (b), (c) are equivalent, "when any one of the conditions
holds" is expressed by quantifying over a stationary distribution `π`. `Nonempty S` is needed:
on an empty type (b) holds vacuously and (c) fails. -/
theorem theorem_C_19 {S : Type*} [Countable S] [Nonempty S] (P : Chain S) (hP : Irreducible P) :
    List.TFAE
        [∃ l : S, meanReturn P {l} l < ⊤,
          PositiveRecurrent P,
          ∃ π : PMF S, IsStationaryChain P π] ∧
      ∀ π : PMF S, IsStationaryChain P π →
        (∀ π' : PMF S, IsStationaryChain P π' → π' = π) ∧
          ∀ i : S, π i = (meanReturn P {i} i)⁻¹ := by sorry

end ProcessingNetworks.CTMCFoster
