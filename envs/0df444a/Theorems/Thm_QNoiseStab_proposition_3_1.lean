-- Prove2me | Theorems.Thm_QNoiseStab_proposition_3_1
-- name    : QNoiseStab.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:06.415771+00:00
-- url     : https://prove2.me/theorems/ac73c007-129d-4bfb-9415-58774cff586a
-- title:
--   Proposition 3.1 — $\Pr[N_p(x)=y]=\langle x|T_p|y\rangle=(1-p)\delta_{x,y}+p/m$
-- statement:
--   Let $m\ge1$, $p\in\mathbb R$ and $T_p=p\,|\hat0\rangle\langle\hat0|+(1-p)I$ on $\mathbb C^{\mathbb Z_m}$. For any $x,y\in\mathbb Z_m$,
--
--   $$
--   \Pr[N_p(x)=y]=\langle x|\,T_p\,|y\rangle=(1-p)\,\delta_{x,y}+\frac pm ,
--   $$
--
--   where $\delta_{x,y}$ is the Kronecker delta.
--
--   So $T_p$ is the Markov transition matrix of the single-coordinate noise $N_p$; the tensor power version is Proposition 3.2.
--
--   Differences from the source:
--   - generalization: $p$ a resampling probability → every real $p$; reason: both equalities are polynomial identities in $p$; the source's $p\in[0,1]$ is a special case
--   - encoding: $\Pr[N_p(x)=y]$ and $\langle x|T_p|y\rangle$ for $x,y\in[m]$ → `coordNoise p x y` (cast to ℂ) and the matrix entry `singleNoiseOp p x y`, $x,y\in$ `ZMod m`; reason: the law of the random variable and the matrix entry are the same numbers
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Proposition 3.1, p.11

import Mathlib
import Definitions.Def_QNoiseStab_coordNoise
import Definitions.Def_QNoiseStab_singleNoiseOp

namespace QNoiseStab

/-- **Proposition 3.1** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.11). For any `x, y ∈ [m]`,
`Pr[N_p(x) = y] = ⟨x| T_p |y⟩ = (1 − p) δ_{x,y} + p/m`, where `T_p = p |0̂⟩⟨0̂| + (1 − p) I`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p(x) = y]` is `coordNoise p x y`, cast to `ℂ`; the
matrix entry `⟨x|T_p|y⟩` is `singleNoiseOp p x y`. Both equalities are identities valid for every
real `p`. -/
theorem proposition_3_1 {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ((coordNoise p x y : ℝ) : ℂ) = singleNoiseOp p x y ∧
      singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by sorry

end QNoiseStab
