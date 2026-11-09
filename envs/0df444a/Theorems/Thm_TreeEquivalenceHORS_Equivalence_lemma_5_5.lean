-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_5
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:43.650906+00:00
-- url     : https://prove2.me/theorems/cb080d0c-670e-47c5-a730-509c5d9bb241
-- title:
--   Lemma 5.5 (All-candidate invariant): continuations preserve $\mathrm{Reg}$, and every candidate prefix is represented
-- statement:
--   Let $G=G^\diamond_M$.
--
--   1. Let $i\in I_M$ be a nonhalting state and $\vec t$ a closed argument tuple. One head step of $F_i\,\vec t$ gives $b\,z\,c_1\,c_2$ with continuations $c_e=F_{\widehat{i_e}}\,\vec t_e$ (Figure 3). If $\mathrm{Reg}_m(\vec t;A,B,W)$ holds, then each continuation argument tuple $\vec t_e$ satisfies $\mathrm{Reg}_{m+1}$ at the natural pairs $R_e$ updated by Equation (21), for both choices $e\in\{1,2\}$.
--   2. Hence every finite candidate prefix $v\in C_M$ has such a representation: the argument tuple reached along $v$ from the start rule satisfies $\mathrm{Reg}_{|v|}$ at the natural pairs reached along $v$.
--
--   There is no legality or nonzero-weight hypothesis: illegal candidates and zero weights are covered.
--
--   Differences from the source:
--   - reading: "each continuation of the corresponding nonhalting state rule satisfies Reg_{m+1} for its updated natural pairs"; "every finite candidate prefix has such a representation" → the continuations are named explicitly: one head step of F_i t⃗ yields b z (F_{î₁} t⃗₁) (F_{î₂} t⃗₂) with t⃗_e = contArgs i e t⃗ (Figure 3), and Reg_{m+1}(t⃗_e; R_e) for each e; the representation of a candidate v is the tuple argsAlong v reached from the start rule, with Reg_{|v|}(argsAlong v; pairsAlong v); reason: makes the objects "continuation" and "representation" of the sentence concrete; the head-step clause is a fact about the Figure 3 templates
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.5, printed p. 19 / PDF p. 21

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.5 (All-candidate invariant)** (printed p. 19 / PDF p. 21). Let `G = G^⋄_M`. For a
nonhalting state `i ∈ I_M`, one head step of the call `Fᵢ t⃗` yields `b z c₁ c₂` whose
continuations are `c_e = F_{î_e} t⃗_e` with `t⃗_e = contArgs i e t⃗`; if `Reg_m(t⃗; A, B, W)` holds,
each continuation satisfies `Reg_{m+1}` at the updated natural pairs `R_e` of Equation (21). Hence
every finite candidate prefix `v ∈ C_M` has such a representation: the argument tuple reached
along `v` from the start rule satisfies `Reg_{|v|}` at the pairs reached along `v`. -/
theorem lemma_5_5 (side : Side) (M : Machine) :
    let G := compile side M
    (∀ (m i : ℕ) (t : StateArgs) (R : PairState), M.Active i → Reg G m t R →
      G.headStep (Tm.apps (.nt (iF i)) t.toList) =
          some (Tm.apps tb [tz, callF M (M.nextPos i .one) (M.contArgs i .one t).toList,
            callF M (M.nextPos i .two) (M.contArgs i .two t).toList]) ∧
        ∀ e : Choice, Reg G (m + 1) (M.contArgs i e t) (M.pairStep m i e R)) ∧
    (∀ v : List Choice, M.IsCand v → Reg G v.length (M.argsAlong v) (M.pairsAlong v)) := by sorry

end TreeEquivalenceHORS.Equivalence
