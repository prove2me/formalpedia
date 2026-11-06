-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_D_2
-- name    : ParetoNCSched.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:28:38.820047+00:00
-- url     : https://prove2.me/theorems/c836b2a2-d6a5-4b28-89ce-a9c2b50cfc8b
-- title:
--   Lemma D.2 — layer accounting $F(t)=\int_0^\infty F_s\,ds$
-- statement:
--   Let $R\ge2$, $p\in(0,\infty)^n$, $\sigma$ a correct order, and $t\ge0$. In the run of $\mathrm{MRC}_R$ write $\ell=\ell(t)$, $k_s=k_s(e(t))$, $\Phi_s=\Phi_s(e(t))$, and $F_s=\sum_{i:\,e_i(t)>s}N(\tau_i(s))$. Then $s\mapsto F_s$ and $s\mapsto\Phi_s$ are integrable on $(0,\infty)$,
--   $$F(t)=\int_0^\infty F_s\,ds\qquad\text{and}\qquad \Phi(e(t))=\int_0^\infty\Phi_s\,ds,$$
--   and for all but finitely many $s\ge0$:
--
--   1. if $s<\ell$: $\Phi_s=\frac{n_s(n_s+1)}{2}$ and $F_s=\Phi_s+\frac{U_s(U_s-1)}{2}$;
--   2. if $s>\ell$: $\Phi_s=\frac{k_s(k_s+1)}{2}$ and $F_s=k_sn_s-\frac{k_s(k_s-1)}{2}$.
--
--   The lemma charges each unit of processing to the layer at which it is given and isolates the Round-Robin overhead $U_s(U_s-1)/2$ of the layers below the level.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: the integral ∫₀^∞ F_s ds and ∫₀^∞ Φ_s ds → Bochner integral over (0, ∞) with integrability as part of the conclusion; reason: a non-integrable function would have integral 0; stating integrability keeps the identity meaningful
--   - encoding: "for all but finitely many s" → for every s ≥ 0 outside some finite set S; reason: the same statement
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
--   - encoding: N(t) = |{j : C_j > t}| (p.15) at a time t → #{i : eᵢ(t) < pᵢ}, the unfinished jobs of the state ⟨t, e(t), F(t)⟩ (`stateAt`); reason: p.17: a job is completed iff eᵢ = pᵢ; on the run eᵢ is continuous and non-decreasing, so eᵢ(t) < pᵢ iff Cᵢ > t
--   - encoding: "the relabelled instance" (σ the identity), job n and the level ℓ of Lemma D.1 → σ kept, job n written σ(n − 1), ℓ the function `levelD`; reason: relabelling only
--   - encoding: F_s, which the statement leaves to its proof → F_s = Σ_{i : eᵢ(t) > s} N(τᵢ(s)) with τᵢ(s) = inf{u : eᵢ(u) > s} (p.22) as a definition (`Fs`, `crossTime`); reason: the page gives the formula only in the proof; the statement needs it to have content
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.2, p.21 (F_s defined in its proof, p.22)

import Mathlib
import Definitions.Def_ParetoNCSched_Fs
import Definitions.Def_ParetoNCSched_Us
import Definitions.Def_ParetoNCSched_ns
import Definitions.Def_ParetoNCSched_Phis
import Definitions.Def_ParetoNCSched_IsCorrect
import Definitions.Def_ParetoNCSched_Phi
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma D.2 (Layer accounting).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, Lemma D.2, p.21: "Let R ≥ 2 and t ≥ 0, and write
ℓ = ℓ(t), k_s = k_s(e(t)) and Φ_s = Φ_s(e(t)). Then F(t) = ∫₀^∞ F_s ds and Φ(e(t)) = ∫₀^∞ Φ_s ds,
where, for all but finitely many s, s < ℓ: Φ_s = n_s(n_s+1)/2, F_s = Φ_s + U_s(U_s−1)/2; s > ℓ:
Φ_s = k_s(k_s+1)/2, F_s = k_s n_s − k_s(k_s−1)/2." Context (Appendix D.1, p.20): a correct predicted
order; `F_s` is defined in the proof (p.22).

**Formalization Note.** `ℓ` is `levelD`, `U_s` is `Us`, `F_s` is `Fs`; the integrals are Bochner
integrals over `(0, ∞)` with integrability in the conclusion; "for all but finitely many s" is "for
every `s ≥ 0` outside a finite set `S`". -/
theorem lemma_D_2 (R : ℝ) (hR : 2 ≤ R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin n)) (hσ : IsCorrect p σ) (t : ℝ) (ht : 0 ≤ t) :
    (IntegrableOn (Fs R p σ t) (Ioi 0) ∧
      costSoFar p (mrcRate R p σ) t = ∫ s in Ioi (0 : ℝ), Fs R p σ t s) ∧
    (IntegrableOn (Phis (fun i => elapsed (mrcRate R p σ) i t)) (Ioi 0) ∧
      Phi (fun i => elapsed (mrcRate R p σ) i t) =
        ∫ s in Ioi (0 : ℝ), Phis (fun i => elapsed (mrcRate R p σ) i t) s) ∧
    ∃ S : Finset ℝ, ∀ s : ℝ, 0 ≤ s → s ∉ S →
      (s < levelD R p σ t →
        Phis (fun i => elapsed (mrcRate R p σ) i t) s = (ns p s : ℝ) * ((ns p s : ℝ) + 1) / 2 ∧
        Fs R p σ t s = Phis (fun i => elapsed (mrcRate R p σ) i t) s +
          (Us R p σ s : ℝ) * ((Us R p σ s : ℝ) - 1) / 2) ∧
      (levelD R p σ t < s →
        Phis (fun i => elapsed (mrcRate R p σ) i t) s =
          (ks (fun i => elapsed (mrcRate R p σ) i t) s : ℝ) *
            ((ks (fun i => elapsed (mrcRate R p σ) i t) s : ℝ) + 1) / 2 ∧
        Fs R p σ t s = (ks (fun i => elapsed (mrcRate R p σ) i t) s : ℝ) * (ns p s : ℝ) -
          (ks (fun i => elapsed (mrcRate R p σ) i t) s : ℝ) *
            ((ks (fun i => elapsed (mrcRate R p σ) i t) s : ℝ) - 1) / 2) := by sorry

end ParetoNCSched
