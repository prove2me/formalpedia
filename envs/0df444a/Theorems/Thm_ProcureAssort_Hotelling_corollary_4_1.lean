-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_corollary_4_1
-- name    : ProcureAssort.Hotelling.corollary_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:48.502162+00:00
-- url     : https://prove2.me/theorems/0d8cea3f-c51b-4759-8352-211e9ba19dfb
-- title:
--   Corollary 4.1 ("if" direction), pp. 21–22 — prices satisfying (10)–(11) decentralize an optimal Cent solution, so OPT(DecLin) = OPT(Cent)
-- statement:
--   Let suppliers have finite type sets $\Theta_i$ of strictly positive costs with pmfs $f_i > 0$ and strictly increasing virtual costs, and let $GCS$ and $\mathcal X$ be arbitrary. Let $(x, t)$ be an optimal solution of Cent (feasible, with objective at least that of every feasible pair). Define the assortment
--   $$q_i(\theta) = 1 \iff x_i(\theta) > 0 \qquad (9)$$
--   and suppose prices $p(\theta)$ satisfy, for every profile $\theta$, every $i$ and every $\theta_i \in \Theta_i$,
--   $$x(\theta) = d(q(\theta), p(\theta)) \quad (10), \qquad T_i(\theta_i) = \sum_{\theta_{-i}} p_i(\theta_i, \theta_{-i})\, x_i(\theta_i, \theta_{-i})\, f_{-i}(\theta_{-i}) \quad (11).$$
--   Then $(q, p, x)$ is feasible for DecLin, its DecLin objective equals the Cent objective of $(x, t)$, and
--   $$OPT(DecLin) = OPT(Cent).$$
--
--   This reduces the comparison of the two problems to the solvability of the linear system (10)–(11) in the prices.
--
--   **Formalization Note** (10) is read as consumer optimality: $x(\theta)$ is a demand for the assortment $q(\theta)$ and prices $p(\theta)$ in the sense of (2). The page assumes $(x, T)$ is *the unique* optimal solution; uniqueness is not used by this direction (footnote 14) and is dropped. The final "if and only if" sentence of the corollary is not stated.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Corollary 4.1, pp. 21–22

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem corollary_4_1
    {n : ℕ} (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ))
    (x t : Profile Θ → Fin n → ℝ) (hfeas : IsCentFeasible f X x t)
    (hopt : ∀ x' t' : Profile Θ → Fin n → ℝ, IsCentFeasible f X x' t' →
      centObj f GCS x' t' ≤ centObj f GCS x t)
    (p : Profile Θ → Fin n → ℝ)
    (h10 : ∀ θ, IsDemand GCS X (Finset.univ.filter (fun i => 0 < x θ i)) (p θ) (x θ))
    (h11 : ∀ i, ∀ c ∈ Θ i,
      interim f (fun θ => p θ i * x θ i) i c = interim f (fun θ => t θ i) i c) :
    IsDecLinFeasible f GCS X (fun θ => Finset.univ.filter (fun i => 0 < x θ i)) p x ∧
      decLinObj f GCS p x = centObj f GCS x t ∧
      optDecLin Θ f GCS X = optCent Θ f GCS X := by sorry

end ProcureAssort.Hotelling
