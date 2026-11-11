-- Prove2me | Theorems.Thm_SumReLU_lemma_4_26
-- name    : SumReLU.lemma_4_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:41.46851+00:00
-- url     : https://prove2.me/theorems/8289de91-d87f-457e-8c90-468bc105e4b5
-- title:
--   Lemma 4.26 — $\mathbb E|\langle F_p(u),W\rangle|^2,\ \mathbb E|\langle F_p(u),W\rangle|^4\le2^{O(p)}\|W\|_F^{2,4}$ and $\mathbb E\|\hat\Phi F_p(u)\otimes\hat\Phi F_p(\bar u)\|_F^2\le k^22^{O(p)}$
-- statement:
--   There is an absolute constant $C$ such that for all $d,p\ge1$, with $u=p+iq$, $p,q$ independent $N(0,I_d)$, and $F_p(u)=u^{\otimes p}/\sqrt{p!}$:
--
--   1. for every complex tensor $W$ of order $p$, $\ \mathbb E\,|\langle F_p(u),W\rangle|^2\le2^{Cp}\|W\|_F^2$;
--   2. for every complex tensor $W$ of order $p$, $\ \mathbb E\,|\langle F_p(u),W\rangle|^4\le2^{Cp}\|W\|_F^4$;
--   3. for every $k$ and every real pseudo-projection $\Phi:(\mathbb R^d)^{\otimes p}\to\mathbb R^k$ with complex extension $\hat\Phi$,
--   $$
--   \mathbb E\,\big\|\hat\Phi(F_p(u))\otimes\hat\Phi(F_p(\bar u))\big\|_F^2\le k^2\,2^{Cp},
--   $$
--
--   and each integrand is integrable. Here $\langle\cdot,\cdot\rangle$ is conjugate-linear in its first argument.
--
--   These bounds control the error of the estimated filtered matrix: the complex Gaussian filter has covariance $2^{O(p)}$, much smaller than a real Gaussian filter would.
--
--   Differences from the source:
--   - encoding: $2^{O(p)}$ in the three bounds → $2^{Cp}$ with one absolute constant $C$ for all three, fixed before $d,p,W,k,\Phi$; reason: big-O convention; a multiplicative constant is absorbed since $p\ge1$
--   - encoding: $\|\hat\Phi_p(F_p(u))\otimes\hat\Phi_p(F_p(\bar u))\|_F^2$ → $\sum_{a,b}|(\hat\Phi F_p(u))_a(\hat\Phi F_p(\bar u))_b|^2$, $\hat\Phi$ the matrix with entries cast to $\mathbb C$, $\bar u$ entrywise conjugate; reason: the Frobenius norm of an outer product; the complex extension of Remark 4.20
--   - encoding: expectations → integrable integrands and Bochner integrals against the probe law; reason: integrability keeps the integrals from being a junk $0$
--   - generalization: Section 4.3's standing assumption $k\le d$ (Remark 4.12, p.34: "Throughout this section, we assume without loss of generality that $k\le d$") → no relation between $d$ and $k$; reason: the bound does not depend on it (the lemma's statement involves only the law of the projections of the probe or of $(x,z)$, not the ambient dimension); the statement specializes to $k\le d$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.26, p.41 (PDF p.43); Lemma 4.17, (21), p.36 (PDF p.38); Definition 4.18, Remark 4.20, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_SumReLU_CTensor
import Definitions.Def_SumReLU_probeLaw
import Definitions.Def_SumReLU_IsPseudoProjection

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Lemma 4.26** (moments of the complex Gaussian filter).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.26, p.41 (PDF p.43): "Let u ∼ U, u = p + iq, p, q ∼ N(0, I_d), and let F_p(u) be the
output of the STC F_p(U) defined in (21) in Lemma 4.17. Then, we have E_{u∼U}[|⟨F_p(u), W⟩|²] ≤
2^{O(p)}‖W‖²_F, E_{u∼U}[|⟨F_p(u), W⟩|⁴] ≤ 2^{O(p)}‖W‖⁴_F. In addition, let Φ̂_p be the complex extension
of a real-valued pseudo-projection from (ℝᵈ)^{⊗p} to ℝᵏ. Then:
E_{u∼U}[‖Φ̂_p(F_p(u)) ⊗ Φ̂_p(F_p(ū))‖²_F] ≤ k² 2^{O(p)}." (21), p.36: F_p(u) = u^{⊗p}/√(p!), p ∈ ℤ₊.

**Formalization Note.**
* One absolute constant `C` for all three bounds, chosen before `d, p, W, k, Φ`; `2^{O(p)}` is
  `2^{Cp}` (a multiplicative constant is absorbed since `p ≥ 1`).
* `⟨·,·⟩` is conjugate-linear in its first argument (`cinner`); `‖Φ̂_p(F_p(u)) ⊗ Φ̂_p(F_p(ū))‖²_F` is
  `∑_{a,b} |(Φ̂F_p(u))_a (Φ̂F_p(ū))_b|²`, with `ū` the entrywise conjugate.
* Section 4.3's standing assumption `k ≤ d` (Remark 4.12, p.34, PDF p.36) is not imposed; the bound
  does not depend on it, and the statement specializes to `k ≤ d`.
* The integrability of each integrand is part of the conclusion (no junk-`0` integral). -/
theorem lemma_4_26 :
    ∃ C : ℝ, ∀ (d p : ℕ), 1 ≤ d → 1 ≤ p →
      (∀ W : CTensor d p,
        Integrable (fun u => ‖cinner (Fp p u) W‖ ^ 2) (probeLaw d) ∧
          ∫ u, ‖cinner (Fp p u) W‖ ^ 2 ∂(probeLaw d) ≤ (2 : ℝ) ^ (C * p) * frob W ^ 2) ∧
      (∀ W : CTensor d p,
        Integrable (fun u => ‖cinner (Fp p u) W‖ ^ 4) (probeLaw d) ∧
          ∫ u, ‖cinner (Fp p u) W‖ ^ 4 ∂(probeLaw d) ≤ (2 : ℝ) ^ (C * p) * frob W ^ 4) ∧
      ∀ (k : ℕ) (Φ : Matrix (Fin k) (Fin p → Fin d) ℝ), IsPseudoProjection Φ →
        Integrable (fun u => ∑ a, ∑ b,
            ‖pseudoApply Φ (Fp p u) a * pseudoApply Φ (Fp p (star u)) b‖ ^ 2) (probeLaw d) ∧
          ∫ u, ∑ a, ∑ b, ‖pseudoApply Φ (Fp p u) a * pseudoApply Φ (Fp p (star u)) b‖ ^ 2
              ∂(probeLaw d) ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (C * p) := by sorry

end SumReLU
