-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_observations_3_2_3_3
-- name    : SmallSecretLWE.Classical.observations_3_2_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:07.831092+00:00
-- url     : https://prove2.me/theorems/216477fc-0780-4361-af54-2854e3dc6531
-- title:
--   Observations 3.2 and 3.3 — triangle and Hölder inequalities for the centered $\ell_p$ 'norm' on $\mathbb Z_q^n$
-- statement:
--   For $x\in\mathbb Z_q^n$ let $\tilde x\in\mathbb Z^n$ be its centered lift (entries in $\{-\lceil q/2\rceil+1,\dots,\lfloor q/2\rfloor\}$) and $\|x\|_p=\|\tilde x\|_p$. Then for every $1\le p\le\infty$ and $u,v\in\mathbb Z_q^n$,
--   $$\|u+v\|_p\le\|u\|_p+\|v\|_p ,$$
--   and for $p,p'\in[1,\infty]$ with $1/p+1/p'=1$,
--   $$\sum_{j=1}^n|\tilde u_j\tilde v_j|\le\|u\|_p\,\|v\|_{p'} .$$
--   These are the two norm-like properties used in the planted-case bound (24)–(26).
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: $\sum_j|u_jv_j|$ for $u,v\in\mathbb Z_q^n$ → $\sum_j|\tilde u_j\tilde v_j|$, the product of the integer centered lifts; reason: the paper applies Hölder to lifts in (25); since the centered value of $u_jv_j$ is at most $|\tilde u_j\tilde v_j|$, this is the stronger of the two readings
--   - encoding: $p,p'\in[1,\infty]$, $1/p+1/p'=1$ → `p p' : ENNReal`, `1 ≤ p`, `p⁻¹ + p'⁻¹ = 1` ($\infty^{-1}=0$); reason: Lean convention; same instances
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), pp. 10–11, Observations 3.2 and 3.3

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Basic

namespace SmallSecretLWE.Classical

/-- Observations 3.2 and 3.3. For `1 ≤ p ≤ ∞` and `u, v ∈ Z_q^n`, `‖u + v‖_p ≤ ‖u‖_p + ‖v‖_p`;
and for `p, p' ∈ [1, ∞]` with `1/p + 1/p' = 1`, `Σ_j |ũ_j ṽ_j| ≤ ‖u‖_p ‖v‖_{p'}`, where `ũ, ṽ`
are the centered lifts. -/
theorem observations_3_2_3_3 :
    (∀ (n q : ℕ) [NeZero q] (p : ENNReal), 1 ≤ p → ∀ u v : Fin n → ZMod q,
      lpNorm p (u + v) ≤ lpNorm p u + lpNorm p v) ∧
    (∀ (n q : ℕ) [NeZero q] (p p' : ENNReal), 1 ≤ p → 1 ≤ p' → p⁻¹ + p'⁻¹ = 1 →
      ∀ u v : Fin n → ZMod q,
        ∑ j, |((u j).valMinAbs : ℝ) * ((v j).valMinAbs : ℝ)| ≤ lpNorm p u * lpNorm p' v) := by sorry

end SmallSecretLWE.Classical
