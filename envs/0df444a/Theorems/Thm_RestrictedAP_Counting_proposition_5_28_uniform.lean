-- Prove2me | Theorems.Thm_RestrictedAP_Counting_proposition_5_28_uniform
-- name    : RestrictedAP.Counting.proposition_5_28_uniform
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:24.987553+00:00
-- url     : https://prove2.me/theorems/d77c3b36-7f41-43b9-bf06-6c606b43084c
-- title:
--   Uniform covariance gap over all alphabet sizes up to $m$
-- statement:
--   This is the fully uniform covariance-gap input to Claim 5.22.
--
--   For every alphabet-size bound $m$ and every $s>0$, there is a single $\eta(m,s)>0$ with the following property. For every $q=q'+1\le m$, every alphabet $\Sigma$ of size $q$, and every distribution $\mu$ on $\Sigma^3$ with no $(\mathbb Z,+)$-embedding, fully supported marginals, and $\mu(t)\ge s$ on its support, every covariance matrix $M=\mathbb E_\mu[WW^*]$ formed from orthonormal nonconstant basis functions as in Proposition 5.28 satisfies
--   $$M\succ0,\qquad M-\eta(m,s)I\succeq0.$$
--
--   The quantifier order is essential: $\eta$ is chosen before $q$, $\Sigma$, $\mu$, and the orthonormal bases. This is the parameter needed by multidimensional reverse hypercontractivity in the uniform Claim 5.22; no exact minimum atom probability is required. When $m=0$, the conclusion is vacuous after its size hypothesis.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://arxiv.org/abs/2608.17365, pp. 48–49, Proposition 5.28 and its compactness conclusion; finite alphabet-size and uniform-atom strengthening required by Claim 5.22 (pp. 43–47)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Theorems.Thm_RestrictedAP_Counting_proposition_5_28_atoms

open ComplexOrder

namespace RestrictedAP.Counting

/-- One covariance gap for all distributions on alphabets of size at most `m` whose nonzero atoms
are bounded below by `s`. -/
theorem proposition_5_28_uniform (m : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (q' : ℕ), q' + 1 ≤ m →
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig = q' + 1 →
      ∀ μ : Sig × Sig × Sig → ℝ, IsDist μ → ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
        (∀ (i : Fin 3) (a : Sig), marginal μ i a ≠ 0) →
      ∀ fb : Fin 3 → Fin (q' + 1) → Sig → ℂ,
        (∀ i a, fb i 0 a = 1) →
        (∀ (i : Fin 3) (j k : Fin (q' + 1)),
          ∑ a, (marginal μ i a : ℂ) * star (fb i j a) * fb i k a = if j = k then 1 else 0) →
        let W : Fin 3 × Fin q' → Sig × Sig × Sig → ℂ :=
          fun ij t => fb ij.1 ij.2.succ (coord3 ij.1 t)
        let Mcov : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ :=
          Matrix.of fun ij kl => ∑ t, (μ t : ℂ) * W ij t * star (W kl t)
        Mcov.PosDef ∧
          (Mcov - (η : ℂ) • (1 : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ)).PosSemidef := by sorry
