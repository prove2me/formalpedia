-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_lemma_1
-- name    : OrgDiversity.Optimal.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:58.850548+00:00
-- url     : https://prove2.me/theorems/a39b22d7-accc-4005-8ca2-c90b57607317
-- title:
--   Lemma 1, p. 16 — thresholds 1/2 ≤ α_het < α_hom < 1 and DM's project choice
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   **Lemma 1.** Under Assumption 1 ($\Gamma\ge F(b_H/2)/F(b_L/2)$), the equations
--   $$\alpha F(\alpha b_L)=(1-\alpha)F((1-\alpha)b_H)\,\Gamma\quad\text{and}\quad \alpha F(\alpha b_H)=(1-\alpha)F((1-\alpha)b_L)\,\Gamma$$
--   have solutions $\alpha_{hom}\in(1/2,1)$ and $\alpha_{het}\in[1/2,1)$. For any such solutions, $1/2\le\alpha_{het}<\alpha_{hom}<1$. For every $\alpha\in(1/2,1]$, DM's choice without information is $d^*_{hom}(\phi)=d^*_{het}(\phi)=1$, and with an informative signal:
--   1. if $\alpha\le\alpha_{het}$: $d^*_{hom}(\sigma)=d^*_{het}(\sigma)=1$ for $\sigma\in\{1,2\}$ (non-reactive in both);
--   2. if $\alpha_{het}<\alpha\le\alpha_{hom}$: $d^*_{hom}(\sigma)=1$ and $d^*_{het}(\sigma)=\sigma$;
--   3. if $\alpha>\alpha_{hom}$: $d^*_{hom}(\sigma)=d^*_{het}(\sigma)=\sigma$ (reactive in both).
--
--   Here $d^*_h(\sigma)$ maximizes DM's expected benefit $p(b,d,\sigma)B$, with ties going to her favourite project 1. The lemma pins down which project is chosen in each region of signal informativeness, which every later comparison of the two organizations depends on.
--
--   **Formalization Note** The existence of the thresholds is stated as two existence conjuncts. The ordering and the choices are then stated for arbitrary solutions, which is equivalent because each defining equation has a unique solution in the given interval.
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 16, Lemma 1 (thresholds defined on pp. 15–16)

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem lemma_1 (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) :
    (∃ a : ℝ, P.IsAlphaHom a) ∧ (∃ a : ℝ, P.IsAlphaHet a) ∧
    ∀ αhom αhet : ℝ, P.IsAlphaHom αhom → P.IsAlphaHet αhet →
      (1 / 2 ≤ αhet ∧ αhet < αhom ∧ αhom < 1) ∧
      ∀ α : ℝ, 1 / 2 < α → α ≤ 1 →
        (dStar P .hom α .phi = .one ∧ dStar P .het α .phi = .one) ∧
        (α ≤ αhet →
          dStar P .hom α .one = .one ∧ dStar P .hom α .two = .one ∧
          dStar P .het α .one = .one ∧ dStar P .het α .two = .one) ∧
        (αhet < α → α ≤ αhom →
          dStar P .hom α .one = .one ∧ dStar P .hom α .two = .one ∧
          dStar P .het α .one = .one ∧ dStar P .het α .two = .two) ∧
        (αhom < α →
          dStar P .hom α .one = .one ∧ dStar P .hom α .two = .two ∧
          dStar P .het α .one = .one ∧ dStar P .het α .two = .two) := by sorry

end OrgDiversity.Optimal
