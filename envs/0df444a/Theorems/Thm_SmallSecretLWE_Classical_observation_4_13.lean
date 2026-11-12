-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_observation_4_13
-- name    : SmallSecretLWE.Classical.observation_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:03.540873+00:00
-- url     : https://prove2.me/theorems/b2757477-025f-4176-847f-487bbb3d444d
-- title:
--   Observation 4.13 — equal hash keys imply $\ell_1$-distance at most $R$
-- statement:
--   Let $0\le R<q/2$ and let $H$ be the hash of Eq. (10) on $(\mathbb Z_q^n)_l$, with bucket width $h=\min\{q-1,\lfloor R/l\rfloor+1\}$. For $x,y\in(\mathbb Z_q^n)_l$,
--   $$H(x)=H(y)\ \Longrightarrow\ \|x-y\|_1\le R .$$
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: $x,y$ and $R$ as set up before Eq. (10) → hypotheses $0\le R<q/2$, $\|x\|_0=\|y\|_0=l$; reason: the standing assumptions of the paragraph defining $H$ (Eq. (10) is defined for $x\in(\mathbb Z_q^n)_l$ and $0\le R<q/2$)
--   - encoding: $H(x)=((j_a)_a,(\lfloor(x_{j_a}-1)/h\rfloor)_a)$ → `hashKey l R x`, the list of pairs $(j_a,\lfloor(x_{j_a}-1)/h\rfloor)$ in increasing $j_a$ (0-based columns); reason: same key up to the bijection between the two encodings
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 18, Observation 4.13 (with Eq. (10))

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- Observation 4.13. Let `0 ≤ R < q/2` and `x, y ∈ (Z_q^n)_l`. If `H(x) = H(y)` for the hash of
Eq. (10), then `‖x − y‖_1 ≤ R`. -/
theorem observation_4_13 {n q : ℕ} [NeZero q] (l : ℕ) (R : ℝ) (hR₀ : 0 ≤ R)
    (hRq : R < (q : ℝ) / 2) (x y : Fin n → ZMod q) (hx : l0 x = l) (hy : l0 y = l)
    (h : hashKey l R x = hashKey l R y) :
    l1 (x - y) ≤ R := by sorry

end SmallSecretLWE.Classical
