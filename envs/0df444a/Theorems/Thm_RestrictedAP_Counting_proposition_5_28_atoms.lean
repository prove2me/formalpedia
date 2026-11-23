-- Prove2me | Theorems.Thm_RestrictedAP_Counting_proposition_5_28_atoms
-- name    : RestrictedAP.Counting.proposition_5_28_atoms
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:12:22.069804+00:00
-- url     : https://prove2.me/theorems/8d2615eb-51a8-4ead-a6b6-223b438069ec
-- title:
--   Proposition 5.28 with a uniform lower bound on atoms
-- statement:
--   This is the uniform-atom strengthening of Proposition 5.28 needed in Claim 5.22.
--
--   Fix an alphabet size $q=q'+1$ and $s>0$. There is $\eta=\eta(s,q)>0$ such that for every alphabet $\Sigma$ of size $q$, every distribution $\mu$ on $\Sigma^3$ with no $(\mathbb Z,+)$-embedding and with $\mu(t)\ge s$ whenever $\mu(t)\ne0$, and every choice of orthonormal bases $f^{(i)}_0=1,f^{(i)}_1,\ldots,f^{(i)}_{q-1}$ for $L^2(\mu_i)$, the covariance matrix
--   $$M=\mathbb E_\mu[WW^*],\qquad
--   W=(f^{(1)}_1(X),\ldots,f^{(1)}_{q-1}(X),f^{(2)}_1(Y),\ldots,f^{(3)}_{q-1}(Z))$$
--   satisfies $M\succ0$ and $M-\eta I\succeq0$. The three marginals are assumed to have full support, as in Proposition 5.28.
--
--   Unlike the existing exact-minimum formulation, this statement does not require $s$ to be attained as the minimum nonzero atom probability. Thus the same $\eta$ applies to every distribution covered by an atom lower bound $s$, which is precisely the uniformity required when Claim 5.22 is quantified over $\mu$.
-- source:
--   Amey Bhangale, Subhash Khot, Yang P. Liu and Dor Minzer, A Counting Lemma for Somewhat Restricted 3-APs, ACM STOC 2027 submission 1020, https://arxiv.org/abs/2608.17365, pp. 48–49, Proposition 5.28 and its closing compactness argument; uniform-atom strengthening required by Claim 5.22 (pp. 43–47)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

open ComplexOrder

namespace RestrictedAP.Counting

/-- Uniform-atom form of Proposition 5.28: the covariance gap depends only on the prescribed
positive lower bound for all nonzero atoms, not on attainment of that bound. -/
theorem proposition_5_28_atoms (q' : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧
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
