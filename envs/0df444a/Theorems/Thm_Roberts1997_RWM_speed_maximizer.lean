-- Prove2me | Theorems.Thm_Roberts1997_RWM_speed_maximizer
-- name    : Roberts1997.RWM.speed_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:50:09.640996+00:00
-- url     : https://prove2.me/theorems/ba9de396-5f4a-4c77-9045-da6783d39998
-- title:
--   Corollary 1.2 (ii) — h(l) is maximized at l̂ = 2.38/√I, with a(l̂) = 0.23 and h(l̂) = 1.3/I
-- statement:
--   Let $I>0$ and, for $l>0$, $h(l)=2l^2\Phi(-l\sqrt I/2)$ and $a(l)=2\Phi(-l\sqrt I/2)$. Then $h$ attains its maximum over $l>0$, and every maximiser $\hat l$ satisfies, to the precision printed in the paper,
--
--   $$ \hat l=\frac{2.38}{\sqrt I},\qquad a(\hat l)=0.23,\qquad h(\hat l)=\frac{1.3}{I}; $$
--
--   precisely,
--
--   1. $2.375\le\hat l\sqrt I<2.385$;
--   2. $0.225\le a(\hat l)<0.235$;
--   3. $1.25\le h(\hat l)\,I<1.35$.
--
--   This is the optimal-scaling statement of the paper: the most efficient limiting diffusion has proposal scale $2.38/\sqrt I$, at which the asymptotic acceptance rate is about $0.23$.
--
--   **Formalization Note** "Maximized (to two decimal places)" is read as: a maximiser over $l>0$ exists, and every maximiser rounds to the printed values; $2.38$ and $0.23$ are rounded to two decimals, and $1.3$, printed with one decimal, to one decimal. The domain is $l>0$ (on $l<0$, $h$ is unbounded). The statement is for an arbitrary constant $I>0$; since $h$ and $a$ depend on $f$ only through $I$, this covers $I=\mathbb E_f[(f'/f)^2]$ for every admissible $f$.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 113, Corollary 1.2 (ii)

import Definitions.Def_Roberts1997_RWM_Speed

namespace Roberts1997.RWM

/-- Corollary 1.2 (ii) (p. 113). For `I > 0`, `h(l) = 2l²Φ(-l√I/2)` attains its maximum over
`l > 0`, and every maximiser `l̂` satisfies, to the printed precision, `l̂ √I = 2.38`,
`a(l̂) = 0.23` and `h(l̂) I = 1.3`. -/
theorem speed_maximizer (I : ℝ) (hI : 0 < I) :
    (∃ lhat : ℝ, 0 < lhat ∧ IsMaxOn (speedI I) (Set.Ioi 0) lhat) ∧
    ∀ lhat : ℝ, 0 < lhat → IsMaxOn (speedI I) (Set.Ioi 0) lhat →
      (2.375 ≤ lhat * Real.sqrt I ∧ lhat * Real.sqrt I < 2.385) ∧
      (0.225 ≤ accRateI I lhat ∧ accRateI I lhat < 0.235) ∧
      (1.25 ≤ speedI I lhat * I ∧ speedI I lhat * I < 1.35) := by sorry

end Roberts1997.RWM
