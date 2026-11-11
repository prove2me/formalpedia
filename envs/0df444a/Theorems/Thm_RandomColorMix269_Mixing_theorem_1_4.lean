-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_theorem_1_4
-- name    : RandomColorMix269.Mixing.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:41.580451+00:00
-- url     : https://prove2.me/theorems/20ebbfd1-4605-447c-a906-a12b2de1c035
-- title:
--   Theorem 1.4 — $\mathrm{CI}(\mu_{G,q})\le C\ln n$ w.h.p. on $G(n,d/n)$ for $q\ge(1+\eta)d$
-- statement:
--   Fix $\eta\in(0,1)$. There is $d_0>1$ such that for every real $d\ge d_0$ there is a constant $C=C(\eta,d)>0$ with the following property. For every integer $q\ge(1+\eta)d$, with probability tending to $1$ as $n\to\infty$ over $G\sim G(n,d/n)$, the graph $G$ is $q$-colourable and the uniform law $\mu_{G,q}$ on its proper $q$-colourings is $(C\ln n)$-coupling independent:
--   $$
--   \mathrm{CI}(\mu_{G,q})\le C\ln n .
--   $$
--   Coupling independence bounds the Hamming $W_1$ distance between the conditional laws under any two feasible pinnings of the same boundary that differ at one coordinate. The constant does not depend on $q$ or $n$. This is the paper's main technical input, from which spectral independence (Corollary 1.5) and then rapid mixing follow.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: statements about the uniform law µ_{G,q}, defined only when G has a proper q-colouring → the high-probability event also contains Colorable G q; reason: without it the zero mass function makes the pinned conditions vacuous; µ_{G,q} is meaningless otherwise
--   - encoding: with probability at least 1 − o_n(1) over G ∼ G(n,d/n), for all sufficiently large n → the probability of the event under LPCommunity.SBMRecovery.erProb n (d/n) tends to 1; reason: the published law clamps d/n to [0,1], which differs from G(n,d/n) only for the finitely many n < d
--   - encoding: CI(µ) ≤ C ln n, CI the minimal coupling-independence constant → µ is (C ln n)-coupling independent; reason: the set of valid constants is closed upward and closed, so the two are equivalent
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.4, Theorem 1.4

import Definitions.Def_RandomColorMix269_Mixing_Independence

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Theorem 1.4, p.4. C is uniform in q as well as n. -/
theorem theorem_1_4 :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ d₀ : ℝ, 1 < d₀ ∧
      ∀ d : ℝ, d₀ ≤ d → ∃ C : ℝ, 0 < C ∧
        ∀ q : ℕ, (1 + η) * d ≤ q →
          WithHighProbability d (fun n G => Colorable G q ∧
            CouplingIndependent (MarkovMixing.properColoringDist G q)
              (C * Real.log n)) := by sorry

end RandomColorMix269.Mixing
