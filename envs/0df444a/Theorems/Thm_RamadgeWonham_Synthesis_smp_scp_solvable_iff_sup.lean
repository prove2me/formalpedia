-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_smp_scp_solvable_iff_sup
-- name    : RamadgeWonham.Synthesis.smp_scp_solvable_iff_sup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:42:44.275266+00:00
-- url     : https://prove2.me/theorems/4374bdbc-b21e-4f72-b739-31a5f6ce3a04
-- title:
--   Theorem 7.1, pp. 218–219 — SMP (SCP) is solvable iff sup C(L_g) (sup{C(L_g) ∩ F(L_g)}) contains L_a, minimally restrictively
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$, trim in the sense $L(\mathcal G) = \bar L_m(\mathcal G)$. Let $L_a, L_g \subseteq \Sigma^*$ satisfy
--
--   $$\emptyset \neq L_a \subseteq L_g \subseteq L_m(\mathcal G).$$
--
--   Then:
--
--   1. the Supervisory Marking Problem is solvable (there is a proper supervisor $\mathcal S$ with $L_a \subseteq L_m(\mathcal S/\mathcal G) \subseteq L_g$) if and only if
--   $$\sup \mathbf C_{\mathcal G}(L_g) \supseteq L_a;$$
--   2. the Supervisory Control Problem is solvable (there is a proper supervisor $\mathcal S$ with $L_a \subseteq L_c(\mathcal S/\mathcal G) \subseteq L_g$) if and only if
--   $$\sup\{\mathbf C_{\mathcal G}(L_g) \cap \mathbf F_{\mathcal G}(L_g)\} \supseteq L_a.$$
--
--   In each case the corresponding supervisor is **minimally restrictive**: when the condition holds there is a solving supervisor $\mathcal S$ with $L_m(\mathcal S/\mathcal G) = \sup \mathbf C_{\mathcal G}(L_g)$ (respectively $L_c(\mathcal S/\mathcal G) = \sup\{\mathbf C_{\mathcal G}(L_g) \cap \mathbf F_{\mathcal G}(L_g)\}$), and for every proper supervisor $\mathcal S'$ whose marked (respectively controlled) language is contained in $L_g$, that language is contained in the one of $\mathcal S$.
--
--   This is the first main result of the paper: the existence of a supervisor meeting a specification reduces to a single inclusion involving the supremal controllable sublanguage, which is also the behaviour of the least restrictive solution.
--
--   **Formalization Note.** All supervisors have accessible automata (the paper's standing assumption) and may have infinitely many states. $\sup$ is `sSup` in `Set (List α)`. Minimal restrictiveness is formalized with the meaning the paper gives on p. 218: the language is as large as possible among proper supervisors subject to being a sublanguage of $L_g$.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, pp. 218–219, Theorem 7.1 (with the §7 hypotheses and the definition of 'minimally restrictive', pp. 217–218)

import Mathlib
import Definitions.Def_RamadgeWonham_Synthesis_Controllable
import Definitions.Def_RamadgeWonham_Synthesis_Problems

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Theorem 7.1, pp. 218–219. Standing assumptions: `Σ` finite (p. 207),
`L(𝒢) = L̄_m(𝒢)` (§5, p. 213), supervisors accessible (p. 210); §7 hypotheses
`∅ ≠ L_a ⊆ L_g ⊆ L_m(𝒢)` (p. 217).
(i) SMP is solvable iff `sup C_𝒢(L_g) ⊇ L_a`; (ii) SCP is solvable iff
`sup (C_𝒢(L_g) ∩ F_𝒢(L_g)) ⊇ L_a`. In each case the corresponding supervisor is minimally
restrictive (p. 218): its `L_m(𝒮/𝒢)` (resp. `L_c(𝒮/𝒢)`) is the supremal element, and it contains
`L_m(𝒮'/𝒢)` (resp. `L_c(𝒮'/𝒢)`) for every proper supervisor `𝒮'` whose marked (resp. controlled)
language is a sublanguage of `L_g`. -/
theorem smp_scp_solvable_iff_sup {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (La Lg : Set (List α))
    (hLa : La.Nonempty) (hLaLg : La ⊆ Lg) (hLg : Lg ⊆ G.Lm) :
    (((∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮) ↔ La ⊆ sSup (Cset G Ec Lg)) ∧
      (La ⊆ sSup (Cset G Ec Lg) →
        ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮 ∧ Shared.Lmsup G 𝒮 = sSup (Cset G Ec Lg) ∧
          ∀ 𝒮' : Shared.Supervisor α Ec, 𝒮'.S.Accessible → Shared.Proper G 𝒮' → Shared.Lmsup G 𝒮' ⊆ Lg →
            Shared.Lmsup G 𝒮' ⊆ Shared.Lmsup G 𝒮)) ∧
    (((∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮) ↔
        La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg)) ∧
      (La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg) →
        ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮 ∧
          Shared.Lcsup G 𝒮 = sSup (Cset G Ec Lg ∩ Fset G Lg) ∧
          ∀ 𝒮' : Shared.Supervisor α Ec, 𝒮'.S.Accessible → Shared.Proper G 𝒮' → Shared.Lcsup G 𝒮' ⊆ Lg →
            Shared.Lcsup G 𝒮' ⊆ Shared.Lcsup G 𝒮)) := by sorry

end RamadgeWonham.Synthesis
