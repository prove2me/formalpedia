-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_lemma_2
-- name    : PayAsBid.SoftReserve.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:48.406984+00:00
-- url     : https://prove2.me/theorems/94c27b3b-ae0f-436d-9ede-7a24a97f9fe9
-- title:
--   Lemma 2, p. A1 — Model 2 is equivalent to α′ = 0, Γ′ = diag(1/δ) with δ = 1/(r_o + r_c)
-- statement:
--   Consider Model 2 with $\alpha=(a,\dots,a)$ and $\Gamma$ equal to $r_o$ on the diagonal and $-r_c$ off it, under the standing assumptions (so $\Gamma$ is positive definite). Let $\delta=1/(r_o+r_c)$ and let the reduced model have $\alpha'=0$ and $\Gamma'=\mathrm{diag}(1/\delta,\dots,1/\delta)$, with the same costs and probabilities. Then:
--
--   1. the reduced model also satisfies the standing assumptions;
--   2. for every nonempty assortment $Q$ and every $p\in\mathbb R^n_+$, a vector solves Problem (1) in the original model if and only if it solves Problem (1) in the reduced model;
--   3. on the simplex the two consumer surpluses differ by a constant: there is $C$ with
--   $$CS(x,p)=CS'(x,p)+C\qquad\text{whenever }\textstyle\sum_i x_i=1.$$
--
--   Part 3 is the computation in the paper's proof, and it is what lets the paper study expected consumer surplus in the reduced model only: demands, allocations and equilibria coincide, and expected surplus is shifted by $C$.
--
--   **Formalization Note.** The reduced model is the parameter record with $a:=0$, $r_o:=r_o+r_c$ ($=1/\delta$) and $r_c:=0$. The inverse $\Gamma^{-1}$ displayed in the paper's proof has its diagonal and off-diagonal entries swapped; the statement does not depend on that display.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. A1 (PDF 34), Lemma 2 and its proof

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem lemma_2 {n : ℕ} (P : Params n) (hP : P.Standing) :
    let P' : Params n := { P with a := 0, ro := P.ro + P.rc, rc := 0 }
    P'.Standing ∧
    (∀ Q : Finset (Fin n), Q.Nonempty → ∀ p : Fin n → ℝ, Nonneg p →
      ∀ x : Fin n → ℝ, IsDemand P Q p x ↔ IsDemand P' Q p x) ∧
    ∃ C : ℝ, ∀ p x : Fin n → ℝ, ∑ i, x i = 1 → CS P x p = CS P' x p + C := by sorry

end PayAsBid.SoftReserve
