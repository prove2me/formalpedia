-- Prove2me | Theorems.Thm_PreservePast_common_output_space
-- name    : PreservePast.common_output_space
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:41:18.867201+00:00
-- url     : https://prove2.me/theorems/da652528-e7f5-468a-93e8-a87bb2c96130
-- title:
--   (63)–(66) — one query-independent output space for $2\le r\le\epsilon^{-2}$
-- statement:
--   Assume one old task ($K=1$), radius $R=\sqrt3$, $2\le r\le\epsilon^{-2}$, $r\le m\le n$ and $0<\epsilon\le2^{-28}$, and let $\mathcal L=\log_2(2/\epsilon)$. There is an absolute constant $C$ such that every task has a subspace $U\subseteq\mathbb R^m$ with
--   $$
--   \dim U\le\min\{m,\ C(r+\epsilon^{-1})\mathcal L^2\}
--   $$
--   with the following property: for every promised unit query $(x,p)$, with $Q=U+\operatorname{span}\{p\}$, some update $H_Q$ satisfies
--   $$
--   H_Qx=p,\qquad\operatorname{rank}H_Q\le r,\qquad\|H_Q\|_F\le\sqrt3,\qquad\operatorname{range}H_Q\subseteq Q,\qquad f(H_Q)\le\epsilon/64 .
--   $$
--
--   The space $U$ is chosen from the task alone, before the query; it replaces the raw loss coefficients as the retained information and is the source of the $\tilde O(n(r+\epsilon^{-1}))$ part of the upper bound.
--
--   **Formalization Note** The proof's auxiliary objective $f_0$ (with covariance $C_h+\alpha I$, $f\le f_0$) is not stated; the conclusion is the bound on the old-loss increment $f$ that the paragraph announces.
--
--   Differences from the source:
--   - reading: f(H_Q) ≤ f₀(H_Q) ≤ ϵ/64 (66), with f₀ the proof's auxiliary objective → f(H_Q) ≤ ϵ/64; reason: the section states the guarantee as 'old-loss increment at most ϵ/64'; f₀ is defined only inside the proof from internal choices (C_h, α)
--   - encoding: dim U ≤ min{m, C(r + ϵ^{−1})𝓛²} with the proof's C → ∃ C chosen before m, n, r, ϵ, W₀ and the task; reason: the paper's C is absolute
--   - generalization: Theorem 4's standing assumption n ≥ N_β (§C.5 is its proof) → no hypothesis n ≥ N_β; reason: the construction of U does not use it, and for m < 2²⁸C the choice U = ℝᵐ with H_Q = H_* already works; adding n ≥ N_β back gives the source's claim
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.5, pp.22–23 (PDF pp.24–25), (63)–(66)

import Mathlib
import Definitions.Def_PreservePast_IsPromised
import Definitions.Def_PreservePast_FC

open Matrix

namespace PreservePast

/-- **The common output space, (63)–(66).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.5, pp.22–23 (PDF pp.24–25), proof of
Theorem 4, case `2 ≤ r ≤ ϵ^{−2}`: "We construct a query-independent output space U such that, after
adding the query direction p, a response with range in U + span{p} satisfies the exact query, rank
and norm constraints with old-loss increment at most ϵ/64. … dim U ≤ min{m, C(r + ϵ^{−1})𝓛²}. (63)
… H_Qx = p, rank H_Q ≤ r, ‖H_Q‖_F ≤ R, range H_Q ⊆ Q, f(H_Q) ≤ f₀(H_Q) ≤ ϵ/64. (66)"

Under Theorem 4's assumptions (`K = 1`, `R = √3`, `r ≤ m ≤ n`, `0 < ϵ ≤ 2^{−28}`) and
`2 ≤ r ≤ ϵ^{−2}`: there is an absolute constant `C` such that every task has a subspace `U ⊆ ℝᵐ` of
dimension at most `min{m, C(r + ϵ^{−1})𝓛²}` for which every promised unit query `(x, p)` admits an
update `H_Q` with `H_Q x = p`, `rank H_Q ≤ r`, `‖H_Q‖_F ≤ √3`, range in `Q = U + span{p}` and
`f(H_Q) ≤ ϵ/64`.

**Formalization Note.** `U` is chosen after the task and before the query. The proof's auxiliary
function `f₀` (with covariance `C_h + αI`) is not stated; the conclusion is the old-loss bound. -/
theorem common_output_space :
    ∃ C : ℝ, ∀ (m n r : ℕ) (ε : ℝ) (W₀ : Matrix (Fin m) (Fin n) ℝ),
      2 ≤ r → (r : ℝ) ≤ 1 / ε ^ 2 → r ≤ m → m ≤ n → 0 < ε → ε ≤ (2 : ℝ) ^ (-28 : ℤ) →
      ∀ T : Task W₀, ∃ U : Submodule ℝ (Fin m → ℝ),
        (Module.finrank ℝ U : ℝ) ≤ min (m : ℝ) (C * ((r : ℝ) + 1 / ε) * calL ε ^ 2) ∧
        ∀ (x : Fin n → ℝ) (p : Fin m → ℝ), IsPromised r (Real.sqrt 3) (fun _ : Fin 1 => T) x p →
          ∃ HQ : Matrix (Fin m) (Fin n) ℝ, HQ *ᵥ x = p ∧ HQ.rank ≤ r ∧
            LowRankMEG.frobNorm HQ ≤ Real.sqrt 3 ∧
            LinearMap.range (Matrix.toLin' HQ) ≤ U ⊔ Submodule.span ℝ {p} ∧
            T.lossInc HQ ≤ ε / 64 := by sorry

end PreservePast
