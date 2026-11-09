-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_6
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:01.776542+00:00
-- url     : https://prove2.me/theorems/9c14a099-3a79-47b7-a2c4-e09ad2167177
-- title:
--   Lemma 5.6 (Operational correspondence): $\mathrm{Obs}_{G^\diamond_M}(F_{\hat i}\,\vec t,w,a)\iff T^\diamond(m,i,R)(w)=a$
-- statement:
--   Let $\vec t$ be a closed argument tuple with $\mathrm{Reg}_m(\vec t;R)$. Then for every natural number $i$ (normalized to $\hat i$), every address $w\in\mathbb N^*$ and every terminal $a\in\Sigma_0$,
--   $$\mathrm{Obs}_{G^\diamond_M}(F_{\hat i}\,\vec t,w,a)\iff T^\diamond(m,i,R)(w)=a.$$
--
--   This turns the head-rewriting behaviour of the compiled scheme into the explicit output trees of Equation (23), including padding and absent addresses.
--
--   Differences from the source:
--   - encoding: V_o = partial maps ℕ* ⇀ Σ₀ with † for undefined → `Val .o = List ℕ → Option (Fin 3)`, `none` = †, `Fin 3` indexing z, a, b; reason: same set of partial maps
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.6, printed p. 19 / PDF p. 21

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.6 (Operational correspondence)** (printed p. 19 / PDF p. 21). If `Reg_m(t⃗; R)`, then for
every address `w` and terminal `a` of `Σ₀`, `Obs_{G^⋄_M}(F_î t⃗, w, a) ⟺ T^⋄(m, i, R)(w) = a`,
for every natural `i` (normalized to `î`). -/
theorem lemma_5_6 (side : Side) (M : Machine) (m i : ℕ) (t : StateArgs) (R : PairState)
    (hR : Reg (compile side M) m t R) (w : List ℕ) (a : Fin 3) :
    (compile side M).Obs (callF M i t.toList) w a.val ↔ Tmap side M m i R w = some a := by sorry

end TreeEquivalenceHORS.Equivalence
