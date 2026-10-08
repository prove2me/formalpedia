-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_gibbard_claim
-- name    : StrategyProofArrow.Correspondence.gibbard_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:49.904272+00:00
-- url     : https://prove2.me/theorems/3a1d8f87-fce6-456b-b7ba-b09390c42f88
-- title:
--   §4, p. 33 (Gibbard) — the relation $P$ of a strategy-proof full-range procedure is a strong order, and $\mu$ underlies $v$ with PO and IIA
-- statement:
--   Let $n\ge2$, $m\ge3$, and let $v:\rho_m^n\to S_m$ be a strict voting procedure that is strategy-proof and has range $T_p=S_m$. Fix any strong order $Q\in\rho_m$, and for each strict ballot set $B$ let $P(B)$ be Gibbard's relation: for $x\neq y$,
--   $$x\,\bar P(B)\,y\iff x=v[\Delta_{xy}(B_1),\dots,\Delta_{xy}(B_n)],$$
--   where $\Delta_{xy}(B_i)$ places $x,y$ on top in the order $B_i$ gives them and the other alternatives below in the order of $Q$. Then $P(B)$ is a strong order for every $B$, so $\mu: B\mapsto P(B)$ is a strict social welfare function, and $\mu$
--
--   1. underlies $v$: $\Psi_{S_m}[\mu(B)]=\{v(B)\}$ for every $B$;
--   2. satisfies Pareto optimality (PO);
--   3. satisfies independence of irrelevant alternatives (IIA).
--
--   The paper cites this from Gibbard's proof of the Gibbard–Satterthwaite theorem and does not prove it; it supplies the existence half of Lemma 8.
--
--   **Formalization Note** The conclusion is stated as the existence of $\mu:\rho_m^n\to\rho_m$ whose relation at $B$ is exactly Gibbard's (`gibbardRel v Q B`, the reflexive closure of $\bar P$), which also asserts that $P(B)$ is a strong order. The hypothesis $T_p=S_m$ is the restriction stated by the paper's "first fact" (p. 33), and $n\ge2$, $m\ge3$ are the standing hypotheses of §4. The claim is stated for every choice of $Q$, which the paper calls arbitrary.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §4, pp. 32–33 (construction of Δ_xy, P, μ; citing Gibbard, Econometrica 41 (1973)); range restriction p. 33

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem gibbard_claim {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v) (hrange : Set.range v = Set.univ)
    (Q : StrongOrder A) :
    ∃ μ : StrongProfile ι A → StrongOrder A,
      (∀ B x y, (μ B).1.rel x y ↔ gibbardRel v Q B x y) ∧
      Underlies μ v ∧ PO μ ∧ IIA μ := by sorry

end StrategyProofArrow.Correspondence
