-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_proposition_2
-- name    : RecallTesting.Duopoly.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:09.642063+00:00
-- url     : https://prove2.me/theorems/4499b280-bf77-48ec-84d2-118848299c84
-- title:
--   Proposition 2, p. 15 — no-firm-test iff θ ∈ θ̃nt, dual-firm-test iff θ ≥ θ̃st, single-firm-test otherwise
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$, and let $\tilde\theta^{st}$ (with denominator $N$) and $\tilde\theta^{nt}=[\underline{\tilde\theta}^{nt},\overline{\tilde\theta}^{nt}]$ (with discriminant $D$) be the cutoffs of (A.3)–(A.4). In the testing game between two identical firms, the pure equilibria are as follows.
--
--   1. **No-firm-test equilibrium.** Neither firm testing is an equilibrium if and only if $\theta\in\tilde\theta^{nt}$, that is, $D\ge0$ and $\underline{\tilde\theta}^{nt}\le\theta\le\overline{\tilde\theta}^{nt}$.
--   2. **Dual-firm-test equilibrium.** Both firms testing is an equilibrium if and only if $N>0$ and $\theta\ge\tilde\theta^{st}$.
--   3. **Single-firm-test equilibrium.** Firm 1 testing while firm 2 does not is an equilibrium if and only if $\theta\le\tilde\theta^{st}$ (read as vacuous when $N\le0$) and $\theta\notin\tilde\theta^{nt}$ in the sense that $\theta\le\underline{\tilde\theta}^{nt}$ or $\theta\ge\overline{\tilde\theta}^{nt}$ whenever $D\ge0$.
--   4. The profile with the roles exchanged is an equilibrium under exactly the same condition.
--   5. The two symmetric equilibria never coexist.
--
--   In words: firms rush to market when the failure probability is in the intermediate range $\tilde\theta^{nt}$, both delay when it is above $\tilde\theta^{st}$, and otherwise exactly one firm tests.
--
--   **Formalization Note** The proposition's "determined by the following regions" is read as an exact characterization of each pure equilibrium (the proof derives each region by an equivalence). An equilibrium is a pure Nash equilibrium with weak best responses. The regions are "mutually exclusive" only away from their boundaries: at $\theta=\tilde\theta^{st}$ or at an endpoint of $\tilde\theta^{nt}$ an asymmetric and a symmetric equilibrium coexist, because the page's own conditions "$\theta\ge\tilde\theta^{st}$" and "$\theta\le\tilde\theta^{st}$" overlap. The statement therefore asserts exclusivity between the two symmetric equilibria, which holds everywhere. The guards $N>0$ and $D\ge 0$ make explicit when the cutoffs are defined.
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 15 (PDF 16), Proposition 2; proof pp. 36–37 (PDF 37–38)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem proposition_2 (P : Params) (hS : P.Standing) :
    (IsNE P false false ↔ 0 ≤ discNT P ∧ thetaNTlo P ≤ P.θ ∧ P.θ ≤ thetaNThi P) ∧
    (IsNE P true true ↔ 0 < denST P ∧ thetaST P ≤ P.θ) ∧
    (IsNE P true false ↔
        (0 < denST P → P.θ ≤ thetaST P) ∧
        (0 ≤ discNT P → P.θ ≤ thetaNTlo P ∨ thetaNThi P ≤ P.θ)) ∧
    (IsNE P false true ↔ IsNE P true false) ∧
    ¬ (IsNE P false false ∧ IsNE P true true) := by sorry

end RecallTesting.Duopoly
