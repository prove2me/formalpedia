-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_lemma_1
-- name    : PuhaWardFluid.Limit.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:16.735845+00:00
-- url     : https://prove2.me/theorems/0137f864-1331-4dcb-a275-9808e51e2368
-- title:
--   Lemma 1, (24) and (26), p. 11 — prelimit dynamic equations for ⟨f, ν^N_j⟩ and ⟨ς, η^N_j⟩
-- statement:
--   Consider the $N$-th queue under an HL control policy. Almost surely, for every class $j$, every $f\in C^1_c([0,H^s_j))$, every $\varsigma\in C^1_c([0,H^r_j))$ and every $t\ge0$,
--   $$\langle f,\nu^N_j(t)\rangle=\langle f,\nu^N_j(0)\rangle+\int_0^t\langle f',\nu^N_j(u)\rangle\,du-\mathcal D^N_j(f,t)+f(0)K^N_j(t),\tag{24}$$
--   $$\langle \varsigma,\eta^N_j(t)\rangle=\langle \varsigma,\eta^N_j(0)\rangle+\int_0^t\langle \varsigma',\eta^N_j(u)\rangle\,du-\mathcal S^N_j(\varsigma,t)+\varsigma(0)E^N_j(t).\tag{26}$$
--   Here $C^1_c([0,H))$ is the set of continuous functions on $[0,H)$ with compact support in $[0,H)$ whose derivative exists on $[0,H)$ and is continuous with compact support; $\nu^N_j$ and $\eta^N_j$ are the age-in-service and potential-queue measures, $K^N_j$ the entry-into-service process, $E^N_j$ the arrival process, and $\mathcal D^N_j(f,t)$, $\mathcal S^N_j(\varsigma,t)$ the departure and potential-reneging marked point processes with marks $f(a^N_{j,i}(s))$, $\varsigma(w^N_{j,i}(s))$.
--
--   These equations are the prelimit counterparts of the fluid equations (46)–(47) and are the starting point for identifying fluid limits.
--
--   **Formalization Note** Only (24) and (26) of Lemma 1 are posed; (23) and (25), with test functions of $(x,t)$, are not. The identities are not part of the HL predicate: they must be derived from the definitions of $\nu^N$, $\eta^N$, $K^N$, $\mathcal D^N$, $\mathcal S^N$. The marked processes are written with the marks at the departure (potential reneging) time, where the age (waiting time) equals the service (patience) time.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 11 (PDF 12), Lemma 1, (24) and (26)

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Lemma 1, (24) and (26)** (p. 11). For an HL control policy of the `N`-th queue, almost surely,
for each class `j`, `f ∈ C¹_c([0, H^s_j))`, `ς ∈ C¹_c([0, H^r_j))` and `t ≥ 0`,
(24) `⟨f, ν^N_j(t)⟩ = ⟨f, ν^N_j(0)⟩ + ∫_0^t ⟨f', ν^N_j(u)⟩ du − 𝒟^N_j(f, t) + f(0) K^N_j(t)`,
(26) `⟨ς, η^N_j(t)⟩ = ⟨ς, η^N_j(0)⟩ + ∫_0^t ⟨ς', η^N_j(u)⟩ du − 𝒮^N_j(ς, t) + ς(0) E^N_j(t)`. -/
theorem lemma_1 {J : ℕ} (L : ClassLaws J) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : QueueSeq J Ω) (N : ℕ+) (hQ : Q.IsHLPolicy L P N) :
    ∀ᵐ ω ∂P, ∀ j : Fin J,
      (∀ f f' : ℝ → ℝ, IsC1c (L.Hs j) f f' → ∀ t : ℝ≥0,
        pair f (Q.nu L N ω t j) =
          pair f (Q.nu L N ω 0 j) + (∫ u in Set.Icc (0 : ℝ) t, pair f' (Q.nu L N ω u.toNNReal j))
            - Q.Dmark L N ω (fun x _ => f x) t j + f 0 * (Q.K N ω t j : ℝ)) ∧
      (∀ ς ς' : ℝ → ℝ, IsC1c (L.Hr j) ς ς' → ∀ t : ℝ≥0,
        pair ς (Q.eta L N ω t j) =
          pair ς (Q.eta L N ω 0 j) + (∫ u in Set.Icc (0 : ℝ) t, pair ς' (Q.eta L N ω u.toNNReal j))
            - Q.Smark L N ω (fun x _ => ς x) t j + ς 0 * (Q.E N ω t j : ℝ)) := by sorry

end PuhaWardFluid.Limit
