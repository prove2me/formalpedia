-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_erlang_integral_identity
-- name    : SRPTManyServer.Collapse.erlang_integral_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:27.697+00:00
-- url     : https://prove2.me/theorems/51145619-f9fc-4877-8e4d-88628bbf4e4b
-- title:
--   Proof of Lemma 4, p. 17 — Erlang's loss formula as $\bigl(\int_0^\infty (1+t/r)^{C} e^{-t}\,dt\bigr)^{-1}$
-- statement:
--   Let $E(r, C)$ denote Erlang's loss formula for offered load $r$ and $C$ servers,
--   $$E(r, C) = \frac{r^C/C!}{\sum_{k=0}^{C} r^k/k!}.$$
--   For every $r > 0$ and every $C \in \mathbb N$,
--   $$E(r, C) = \left(\int_0^\infty \Bigl(1 + \frac tr\Bigr)^{C} e^{-t}\,dt\right)^{-1}.$$
--   In particular, when the offered load equals the number of servers, $r = C \ge 1$,
--   $$E(C, C) = \left(\int_0^\infty \Bigl(1 + \frac tC\Bigr)^{C} e^{-t}\,dt\right)^{-1}.$$
--
--   In the paper this is the blocking probability $\mathrm{Pb}^\lambda$ of the class 1 loss queue, whose offered load is $r = \lambda G(\tau)\mathbb E[S \mid S \le \tau] = s^\lambda$ by (1). The integral form is what makes its limit as $s^\lambda \to \infty$ transparent.
--
--   **Formalization Note** $E(r, C)$ is the published definition `KellyStochasticNetworks.erlang`. The integral is over $(0, \infty)$.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 17, proof of Lemma 4 (display defining Pb^λ)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace SRPTManyServer.Collapse

/-- **Erlang's formula as an integral** (proof of Lemma 4, p. 17). For an offered load `r > 0` and
`C` servers, the Erlang loss probability `E(r, C) = (r^C/C!) / ∑_{k=0}^C r^k/k!` equals
`(∫_0^∞ (1 + t/r)^C e^{-t} dt)⁻¹`; in particular, at `r = C ≥ 1`,
`E(C, C) = (∫_0^∞ (1 + t/C)^C e^{-t} dt)⁻¹`. -/
theorem erlang_integral_identity :
    (∀ (r : ℝ), 0 < r → ∀ C : ℕ,
      KellyStochasticNetworks.erlang r C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / r) ^ C * Real.exp (-t))⁻¹) ∧
    (∀ C : ℕ, 1 ≤ C →
      KellyStochasticNetworks.erlang (C : ℝ) C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / (C : ℝ)) ^ C * Real.exp (-t))⁻¹) := by sorry

end SRPTManyServer.Collapse
