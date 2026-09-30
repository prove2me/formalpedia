-- Prove2me | Theorems.Thm_RevenueManagement_bertrand_edgeworth_pure_equilibria
-- name    : RevenueManagement.bertrand_edgeworth_pure_equilibria
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:06:57.031108+00:00
-- url     : https://prove2.me/theorems/3c77903c-429b-4a9b-9e8f-d22074e88f88
-- title:
--   Theorem 8.5 (i)-(ii): under efficient rationing and linear demand, all firms pricing at c is an equilibrium when C ≥ (a − c)/(n − 1), and all pricing at a − nC when C ≤ (a − c)/(n + 1)
-- statement:
--   In the Bertrand–Edgeworth game of $n \ge 2$ firms with linear demand $d(p) = a - p$,
--   $a > c$, capacity $C > 0$ each and the efficient-rationing rule: (i) if
--   $C \ge (a - c)/(n - 1)$, every firm pricing at marginal cost $c$ is a pure-strategy
--   equilibrium and all firms make zero profit; (ii) if $C \le (a - c)/(n + 1)$, every firm
--   pricing at the market-clearing price $a - nC$ is a pure-strategy equilibrium. Part (iii),
--   the mixed-strategy equilibrium of the intermediate range, is not part of this statement.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 386, Theorem 8.5 (i) and (ii) (from Levitan and Shubik, Kreps and Scheinkman, Brock and Scheinkman)

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem bertrand_edgeworth_pure_equilibria {n : ℕ} (hn : 2 ≤ n) (a c C : ℝ) (hac : c < a)
    (hC : 0 < C) :
    ((a - c) / (n - 1) ≤ C →
      IsBEEquilibrium a c C (fun _ : Fin n => c) ∧ ∀ i, bePayoff a c C (fun _ : Fin n => c) i = 0) ∧
    (C ≤ (a - c) / (n + 1) → IsBEEquilibrium a c C (fun _ : Fin n => a - n * C)) := by sorry

end RevenueManagement
