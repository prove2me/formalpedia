-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_hotDemand_isDemand
-- name    : ProcureAssort.Hotelling.hotDemand_isDemand
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:38.967987+00:00
-- url     : https://prove2.me/theorems/acc26a33-f72f-4a2a-96f9-e2049bd52a65
-- title:
--   §3.2.1, pp. 15–16, and App. F.1, p. 40 — the explicit Hotelling demand maximizes consumer surplus over the simplex
-- statement:
--   Consider the general Hotelling model with $n \ge 2$ suppliers at $0 \le \ell_1 < \dots < \ell_n \le 1$, transportation cost $\delta > 0$, unit mass of consumers uniform on $[0,1]$, and no outside option. For any price vector $p \in \mathbb R^n$, let $Q(p) = \{i : p_i \le \min_{k \ne i}(p_k + \delta|\ell_k - \ell_i|)\}$ and let $d(p)$ be the Hotelling demand: $d_i(p) = 0$ for $i \notin Q(p)$, and for $i \in Q(p)$ with left and right active neighbours $L$, $R$,
--   $$d_i(p) = \Big[\ell_i \ \text{or}\ \tfrac{p_L - p_i + \delta|\ell_i - \ell_L|}{2\delta}\Big] + \Big[1 - \ell_i \ \text{or}\ \tfrac{p_R - p_i + \delta|\ell_R - \ell_i|}{2\delta}\Big],$$
--   the first alternative applying when $i$ is the leftmost (resp. rightmost) active supplier. Then $d(p)$ lies in the simplex and
--   $$d(p) \in \operatorname{argmax}_{x \in \mathcal X} \big(GCS(x) - p \cdot x\big),$$
--   i.e. it is a consumer-optimal demand when all products are offered.
--
--   This is the paper's description of the Hotelling demand ("two consecutive suppliers $i, j \in Q(p)$ split the segment between $\ell_i$ and $\ell_j$ … $i$ obtains $(p_j - p_i + \delta|\ell_j - \ell_i|)/(2\delta)$ and $j$ the rest"), and it is what makes $x^\star(\theta) = d(v(\theta))$ the centralized optimum.
--
--   **Formalization Note** The page's "positive demand if and only if $i \in Q(p)$" is not asserted: at a tie $p_i = p_k + \delta|\ell_k - \ell_i|$ supplier $i$ is in $Q(p)$ with zero demand, and with interior locations the argmax is then not unique; the statement claims only that the explicit $d(p)$ is one maximizer.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), §3.2.1, pp. 15–16 (Q(p), split rule) and Appendix F.1, p. 40 (Hotelling demands of active suppliers)

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem hotDemand_isDemand
    (n : ℕ) (hn : 2 ≤ n)
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) :
    IsDemand (hotGCS ℓ δ) (simplex n) Finset.univ p (hotDemand ℓ δ p) := by sorry

end ProcureAssort.Hotelling
