-- Prove2me | Theorems.Thm_PrivLearn_Parity_theorem_4_4
-- name    : PrivLearn.Parity.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:21.186212+00:00
-- url     : https://prove2.me/theorems/caa5315a-4496-4426-b2be-d09c26d883cd
-- title:
--   Theorem 4.4 — $\mathcal A^*$ privately PAC learns PARITY with $O(d\log(1/\beta)/(\varepsilon\alpha))$ samples
-- statement:
--   There are constants $c, c'$ of the algorithm $\mathcal A^*$ and a constant $C > 0$ such that for all $d \ge 1$, $0 < \varepsilon \le 1/2$ and $\alpha, \beta \in (0, 1/2)$:
--
--   1. **(Privacy)** for every database size $n$, $\mathcal A^*(\cdot, \varepsilon, \alpha, \beta)$ is $\varepsilon$-differentially private;
--   2. **(Utility)** for every distribution $\mathcal X$ on $\{0,1\}^d$, every target $c_r \in$ PARITY and every
--   $$
--   n \ge C\,\frac{(d + \log_2(1/\beta))\log_2(1/\beta)}{\varepsilon\alpha},
--   $$
--   on the database $z_i = (x_i, c_r(x_i))$ with $x_1,\dots,x_n \sim \mathcal X$ i.i.d., $\mathcal A^*$ outputs a hypothesis $h^*$ with $\mathrm{err}(h^*) \le \alpha$ with probability at least $1 - \beta$.
--
--   When $\log_2(1/\beta) \le d$ the bound is $O(d\log(1/\beta)/(\varepsilon\alpha))$, the paper's. Parity functions are thus privately PAC learnable (Definition 3.1) with a sample complexity that exceeds the non-private $O((d + \ln(1/\beta))/\alpha)$ by a factor $O(\ln(1/\beta)/\varepsilon)$.
--
--   **Formalization Note** "Efficiently" (polynomial running time) is not modelled. Privacy is stated for $0 < \varepsilon \le 1/2$, the range the paper's proof of Lemma 4.2 covers. The printed sample bound is false when $\log(1/\beta) \gg d$ (the threshold $kn'+s$ of step 2 grows like $\log^2(1/\beta)/(\varepsilon\alpha)$); utility is stated with the corrected bound $C(d + \log_2(1/\beta))\log_2(1/\beta)/(\varepsilon\alpha)$, which reduces to the printed order when $\log_2(1/\beta) \le d$. The privacy conjunct does not depend on the sample bound. $\log$ is base 2, and the base of $k$'s logarithm is corrected from $3/4$ to $4/3$ (see the definition of $\mathcal A^*$).
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 17, Theorem 4.4

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Learner
import Definitions.Def_PrivLearn_Parity_Amplified

namespace PrivLearn.Parity

/-- Theorem 4.4, p. 17. There are constants `c, c′` of algorithm `A*` and a constant `C` such that
for all `d ≥ 1`, `0 < ε ≤ 1/2` and `α, β ∈ (0, 1/2)`:
(privacy) `A*(·, ε, α, β)` is ε-differentially private on databases of every size;
(utility) for every distribution `𝒳` on `{0,1}^d`, every target `c_r ∈ PARITY` and every
`n ≥ C (d + log₂(1/β)) log₂(1/β)/(εα)` (which is `O(d log(1/β)/(εα))` when `log₂(1/β) ≤ d`),
`A*` outputs a hypothesis `h*` with `err(h*) ≤ α` with probability at least `1 − β` over
`x_1, …, x_n ∼ 𝒳` i.i.d. and its coins. -/
theorem theorem_4_4 :
    ∃ c c' C : ℝ, 0 < c ∧ 0 < c' ∧ 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε α β : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algAstar c c' d ε α β z) ε) ∧
        (∀ (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) (n : ℕ),
          C * (d + Real.logb 2 (1 / β)) * Real.logb 2 (1 / β) / (ε * α) ≤ n →
          ENNReal.ofReal (1 - β) ≤
            samplePr 𝒳 r (fun z : Fin n → Example d => algAstar c c' d ε α β z)
              {o | ∃ r' : Fin d → ZMod 2, o = AstarOut.hyp r' ∧ err 𝒳 r (some r') ≤ α}) := by sorry

end PrivLearn.Parity
