-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_theorem_1
-- name    : TensorRankN2M.ThreeTwoM.theorem_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T04:16:15.525944+00:00
-- url     : https://prove2.me/theorems/551e98ee-be20-4cbb-96eb-4a88ab0cc16d
-- title:
--   Theorem 1 — over every field, R(⟨3,2,m⟩) ≥ ⌈(24m+2)/5⌉ for all m ≥ 3
-- statement:
--   Let $\mathbb F$ be any field (finite fields and characteristic $2$ included) and $m\ge 3$ a natural number. Every $R$-rank decomposition of the $\langle 3,2,m\rangle$ matrix multiplication tensor over $\mathbb F$ — linear forms $\alpha_r$ on $\mathbb F^{3\times 2}$, $\beta_r$ on $\mathbb F^{2\times m}$ and matrices $C_r\in\mathbb F^{3\times m}$, $0\le r<R$, with $AB=\sum_r\alpha_r(A)\beta_r(B)C_r$ for all $A,B$ — has $R\ge\lceil(24m+2)/5\rceil$; equivalently, the rank satisfies
--   $$R(\langle 3,2,m\rangle)\ \ge\ \left\lceil\frac{24m+2}{5}\right\rceil .$$
--
--   Combined with the Hopcroft–Kerr upper bound $R(\langle n,2,m\rangle)\le\lceil(3nm+\max(n,m))/2\rceil$, this determines $R(\langle 3,2,m\rangle)=15,20,25,30$ for $m=3,4,5,6$; it improves the earlier bounds $\lceil 24m/5\rceil$ and $\lceil(24m+1)/5\rceil$ and Bläser's bound $R(\langle 2,n,m\rangle)\ge nm+n+m-1$ at $n=3$.
--
--   Differences from the source:
--   - encoding: R(⟨3,2,m⟩), the smallest R admitting a decomposition → tensorRank 𝔽 3 2 m = sInf {R | Nonempty (Decomposition 𝔽 3 2 m R)}; reason: the set is nonempty (R = 6m works), so sInf is the minimum
--   - encoding: terms 0 ≤ r < R, linear forms, matrices → Fin R, →ₗ[𝔽] 𝔽, Matrix (Fin 3) (Fin 2) 𝔽 etc.; ⌈(24m+2)/5⌉ → ⌈(24 * (m : ℚ) + 2) / 5⌉₊ (Nat.ceil); reason: Lean convention, same numbers
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 2, Theorem 1 (abstract p. 1: over an arbitrary field)

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition

namespace TensorRankN2M.ThreeTwoM

/-- Theorem 1 (p. 2): over every field `𝔽` and for every `m ≥ 3`, the rank of the ⟨3,2,m⟩ matrix
multiplication tensor (the least `R` admitting an `R`-rank decomposition) is at least
`⌈(24m+2)/5⌉`. -/
theorem theorem_1 {𝔽 : Type*} [Field 𝔽] (m : ℕ) (hm : 3 ≤ m) :
    ⌈(24 * (m : ℚ) + 2) / 5⌉₊ ≤ tensorRank 𝔽 3 2 m := by sorry

end TensorRankN2M.ThreeTwoM
