-- Prove2me | Theorems.Thm_PrivLearn_Parity_lemma_4_6
-- name    : PrivLearn.Parity.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:18.184057+00:00
-- url     : https://prove2.me/theorems/4a7e5495-aa67-4046-a5cb-1fa448ec4299
-- title:
--   Lemma 4.6 — $\mathcal A^*$ PAC learns PARITY from $C(d+\log_2(1/\beta))\log_2(1/\beta)/(\varepsilon\alpha)$ examples (corrected bound)
-- statement:
--   There are constants $c, c', C > 0$ such that the following holds. Let $d \ge 1$, $0 < \varepsilon \le 4$ and $\alpha, \beta \in (0, 1/2)$. Let $\mathcal X$ be any distribution on $\{0,1\}^d$, $c_r \in$ PARITY any target, and
--
--   $$
--   n \ge C\, \frac{(d + \log_2(1/\beta)) \log_2(1/\beta)}{\varepsilon\alpha}.
--   $$
--
--   If $z_i = (x_i, c_r(x_i))$ with $x_1,\dots,x_n$ i.i.d. from $\mathcal X$, then the output $h^*$ of $\mathcal A^*(z,\varepsilon,\alpha,\beta)$ (with constants $c, c'$) satisfies
--
--   $$
--   \Pr\big[h^* = c_{r'} \text{ for some } r' \text{ with } \mathrm{err}(c_{r'}) \le \alpha\big] \ge 1 - \beta,
--   $$
--
--   the probability being over the examples and all coins of $\mathcal A^*$.
--
--   This is the utility half of Theorem 4.4. When $\log_2(1/\beta) \le d$ the bound is at most $2C\,d\log_2(1/\beta)/(\varepsilon\alpha)$, the paper's $O(d\log(1/\beta)/(\varepsilon\alpha))$.
--
--   **Formalization Note** The paper's sample bound $O(d\log(1/\beta)/(\varepsilon\alpha))$ is false as printed when $\log(1/\beta)$ is large compared with $d$: $\mathcal A^*$ answers "insufficient samples" unless $n > kn' + s$, and $s$ grows like $\log^2(1/\beta)/(\varepsilon\alpha)$, so for fixed $d$ and $\beta \to 0$ no constant $C$ works. The paper's proof never checks $n > kn' + s$. We state the closest true version the proof supports: the bound $C(d + \log_2(1/\beta))\log_2(1/\beta)/(\varepsilon\alpha)$, which is the order of the threshold $kn' + s$ and coincides with the printed order whenever $\log_2(1/\beta) \le d$. The constants are chosen once, before every other quantifier. "insufficient samples" and $\bot$ count as failures. $\varepsilon \le 4$ is all utility needs ($p = \varepsilon/4$ is a probability). The proof's final count "$1 - 3\beta' = 1 - \beta$" is a slip for $\beta' = \beta/2$; the statement is still true with suitable $c'$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 17, Lemma 4.6 (proof pp. 17–18)

import Mathlib
import Definitions.Def_PrivLearn_Parity_Learner
import Definitions.Def_PrivLearn_Parity_Amplified

namespace PrivLearn.Parity

/-- Lemma 4.6 (Utility of A*), p. 17, with the corrected sample bound. There are constants
`c, c′, C > 0` such that for all `d ≥ 1`, `0 < ε ≤ 4`, `α, β ∈ (0, 1/2)`,
every distribution `𝒳` on `{0,1}^d`, every target `c_r ∈ PARITY` and every
`n ≥ C (d + log₂(1/β)) log₂(1/β)/(εα)` (which is `O(d log(1/β)/(εα))` when
`log₂(1/β) ≤ d`), the output `h*` of `A*(z, ε, α, β)` on `z_i = (x_i, c_r(x_i))`,
`x_i ∼ 𝒳` i.i.d., is a hypothesis with `err(h*) ≤ α` with probability at least `1 − β`. -/
theorem lemma_4_6 :
    ∃ c c' C : ℝ, 0 < c ∧ 0 < c' ∧ 0 < C ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε α β : ℝ, 0 < ε → ε ≤ 4 → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        ∀ (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2) (n : ℕ),
          C * (d + Real.logb 2 (1 / β)) * Real.logb 2 (1 / β) / (ε * α) ≤ n →
          ENNReal.ofReal (1 - β) ≤
            samplePr 𝒳 r (fun z : Fin n → Example d => algAstar c c' d ε α β z)
              {o | ∃ r' : Fin d → ZMod 2, o = AstarOut.hyp r' ∧ err 𝒳 r (some r') ≤ α} := by sorry

end PrivLearn.Parity
