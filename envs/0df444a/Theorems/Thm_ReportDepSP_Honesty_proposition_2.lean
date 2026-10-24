-- Prove2me | Theorems.Thm_ReportDepSP_Honesty_proposition_2
-- name    : ReportDepSP.Honesty.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:59.749108+00:00
-- url     : https://prove2.me/theorems/e4ab7b8a-d27e-4e50-958f-be4744ddfb8a
-- title:
--   Proposition 2, p. 7 — the truth beats R̃ for all decreasing ρ iff (3) holds; hence truth is optimal for all ρ iff (3) holds against every R̃
-- statement:
--   A participant ranks $n$ options, labelled so that her report-independent payoffs satisfy $v_1\ge v_2\ge\dots\ge v_n$; the true ROL is $R=(1,2,\dots,n)$. Let $P$ be an attainability distribution, i.e. a probability distribution on the states $\{0,1\}^n$ recording which options are attainable, with arbitrary correlation. Under a ROL $\widetilde R$ the participant is matched with her highest-ranked attainable option, so her $r$-th ranked option $\widetilde r$ is matched with probability $\widetilde f_r = P(A_{\widetilde r}=1, A_{\widetilde t}=0\ \forall t<r)$, and her expected payoff is $U(v\mid\widetilde R) = \sum_{r=1}^n \widetilde f_r\,(v_{\widetilde r}+\rho(r))$ for a report-dependent payoff $\rho$.
--
--   **Proposition 2.**
--
--   1. For every non-truthful ROL $\widetilde R \ne R$: $U(v\mid R)\ge U(v\mid\widetilde R)$ for all strictly decreasing $\rho$ if and only if
--   $$\sum_{r=1}^{\bar r}\Bigl(P(A_r=1, A_t=0\ \forall t<r) - P(A_{\widetilde r}=1, A_{\widetilde t}=0\ \forall t<r)\Bigr)\ \ge\ 0 \qquad \forall\,\bar r\in⟦1,n⟧. \tag{3}$$
--   2. Hence the true ROL is optimal, $U(v\mid R)\ge U(v\mid\widetilde R)$ for all $\widetilde R\ne R$, for every strictly decreasing $\rho$, if and only if (3) holds against every non-truthful ROL $\widetilde R$.
--
--   Truthful reporting is robust to every report-dependent payoff exactly when no alternative list raises the probability of being matched with one of the top $\bar r$ ranked options, for any $\bar r$. When some list does (for instance, ranking a safe option first), a strong enough taste for being accepted by a highly ranked option makes misreporting optimal even in a strategy-proof mechanism.
--
--   **Formalization Note** Options and ranks are 0-indexed `Fin n`; a ROL is `Equiv.Perm (Fin n)` read as option ↦ rank, and the true ROL is `1`; "non-truthful" is `Rt ≠ 1`. "Decreasing functions ρ" is read as strictly decreasing (`StrictAnti ρ`), the model's standing assumption (§2 and footnote 6); the equivalence holds verbatim for weakly decreasing $\rho$ as well. The ordering $v_1\ge\dots\ge v_n$ is the paper's standing relabeling (p. 5) and is a hypothesis. The paper's normalizations $v_n = 0$ (p. 5) and $\rho(1)>0>\rho(n)$ (p. 4) are not imposed: every ROL has the same total match probability, so $U(v\mid R)-U(v\mid\widetilde R)$ is unchanged when a constant is added to $v$ or to $\rho$, and the statement with these normalizations is equivalent to the one without. Condition (3) is the definition `Condition3` with `rbar : Fin n` the page's $\bar r$ shifted by one.
-- source:
--   Meisner, Report-dependent utility and strategy-proofness, CRC TRR 190 Discussion Paper No. 289 (2021; Management Science doi:10.1287/mnsc.2022.4504), Proposition 2, p. 7; model §2, pp. 4–5

import Mathlib
import Definitions.Def_ReportDepSP_Honesty_Setting

namespace ReportDepSP.Honesty

open Finset

/-- Proposition 2 (Meisner, p. 7). For an attainability distribution `P` and a payoff vector `v`
listed in decreasing order (so that the true ROL is `1`): for every non-truthful ROL `Rt`, the truth
is weakly better than `Rt` for every strictly decreasing `ρ` iff condition (3) holds; hence the
truth is optimal (2) for every such `ρ` iff (3) holds against every non-truthful ROL. -/
theorem proposition_2 {n : ℕ} (P : (Fin n → Bool) → ℝ) (hP : IsAttainabilityDist P)
    (v : Fin n → ℝ) (hv : Antitone v) :
    (∀ Rt : Equiv.Perm (Fin n), Rt ≠ 1 →
      ((∀ ρ : Fin n → ℝ, StrictAnti ρ → payoff v ρ P Rt ≤ payoff v ρ P 1) ↔
        Condition3 P Rt)) ∧
    ((∀ ρ : Fin n → ℝ, StrictAnti ρ →
        ∀ Rt : Equiv.Perm (Fin n), Rt ≠ 1 → payoff v ρ P Rt ≤ payoff v ρ P 1) ↔
      ∀ Rt : Equiv.Perm (Fin n), Rt ≠ 1 → Condition3 P Rt) := by sorry

end ReportDepSP.Honesty
