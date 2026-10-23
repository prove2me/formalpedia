-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_3
-- name    : RobustPrefLearn.MTP.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:03.698958+00:00
-- url     : https://prove2.me/theorems/92580e63-760c-49cd-bb38-1b8ff5aa72ef
-- title:
--   Theorem 3, p. 15 — the OA preferences minimize Chernoff's information over M_p
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. For every ranking $\sigma$, the OA preference $f^{\mathrm{OA}}_\sigma$ of (3) belongs to $\mathcal M_p$ and
--   $$I_*(f^{\mathrm{OA}}_\sigma)\le I_*(f)\qquad\text{for every } f\in\mathcal M_p,$$
--   that is, $\mathcal M^{\mathrm{OA}}_p\subseteq\arg\min_{f\in\mathcal M_p}I_*(f)$.
--
--   The OA preferences are therefore the hardest-to-learn preferences in the class, and the worst-case sample complexity is governed by $I^{\mathrm{OA}}_*$.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 15, Theorem 3, (3)–(4)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Theorem 3, p. 15. Every OA preference `f^OA_σ` of (3) lies in `M_p` and minimizes Chernoff's
information `I_*` over `M_p`: `M^OA_p ⊆ argmin_{f ∈ M_p} I_*(f)`. -/
theorem theorem_3 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (σ : Equiv.Perm (Fin K)) :
    oa p σ ∈ (Mp p : Set (Pref K)) ∧ ∀ f ∈ (Mp p : Set (Pref K)), Istar p (oa p σ) ≤ Istar p f := by sorry

end RobustPrefLearn.MTP
