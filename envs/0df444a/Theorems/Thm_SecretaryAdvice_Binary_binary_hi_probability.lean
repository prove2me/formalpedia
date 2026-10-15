-- Prove2me | Theorems.Thm_SecretaryAdvice_Binary_binary_hi_probability
-- name    : SecretaryAdvice.Binary.binary_hi_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:46.594978+00:00
-- url     : https://prove2.me/theorems/9741b769-51f9-4a66-859f-0187471b6fd1
-- title:
--   §2.2, p. 9 — corrected history-irrelevance probability for binary advice
-- statement:
--   Fix a round $i$ and any information state $x$ comprising the observed relative order and signals. If the current secretary is not best so far, the probability that this secretary has the highest rank and that the information state is $x$ is zero. If the current secretary is best so far, let $G$ be $p$ when its signal is $Y$ and $1-p$ when it is $N$; let $B$ be $1-p'$ when its signal is $Y$ and $p'$ when it is $N$. Writing $M(x)$ for the mass of information state $x$ and $M_*(x)$ for the mass where the current secretary is also globally best, the corrected identity is
--
--   $$M_*(x)\,[iG+(n-i)B]=M(x)\,iG.$$
--
--   Thus, whenever $M(x)>0$, the chance that the current secretary is globally best depends only on its round, whether it is best so far, and its current signal. This is the history-irrelevance property used in the LP reduction.
--
--   **Formalization Note** The paper's displayed fractions on p. 9 omit the factor $i$; they are incorrect for $i>1$. The statement uses the corrected values and cross-multiplies, so it also covers information states of zero mass without dividing by zero. Lean indexes rounds from zero, and `i.val + 1` is the paper's $i$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 9, §2.2, paragraph beginning 'For Example 5' (printed formula corrected)

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_Setting

namespace SecretaryAdvice.Binary

/-- Example 5 and §2.2, p. 9: corrected conditional top-rank probability.
The printed display omits the factor `i` in the numerator and denominator. -/
theorem binary_hi_probability (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1)
    (i : Fin n) (x : Info n i) :
    let seen := mass p p' (fun ω => info i ω = x)
    let top := mass p p' (fun ω => info i ω = x ∧ isTop ω i)
    let good := if x.2 (Fin.last i.val) then p else 1 - p
    let other := if x.2 (Fin.last i.val) then 1 - p' else p'
    (¬ bestSoFar i x → top = 0) ∧
    (bestSoFar i x →
      top * (((i.val + 1 : ℕ) : ℝ) * good + ((n - (i.val + 1) : ℕ) : ℝ) * other) =
      seen * (((i.val + 1 : ℕ) : ℝ) * good)) := by sorry

end SecretaryAdvice.Binary
