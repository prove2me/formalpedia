-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_3
-- name    : SwitchingStable.Universal.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:17.407565+00:00
-- url     : https://prove2.me/theorems/811042d4-3cbd-4484-a1a9-26de7fb3c10c
-- title:
--   Lemma 3 — Reveal interval and geometric reference cost
-- statement:
--   Fix a stable matching $\mu$, a man $u$ in position $q$ of his stable list, and revealed men $P\subseteq U\setminus\{u\}$. Let $L$ and $R$ be the nearest revealed owner indices below and above $q$, using sentinels $-1,d_u$. Every stable matching agreeing with $\mu$ on $P$ has its index strictly between them, and
--   $$X_u\le R-L-1.$$
--   Conditional on $T_u=x\in(0,1)$, this interval bound is stochastically dominated by $N_x=G_x^-+G_x^+-1$, with independent positive geometric variables of parameter $x$. In particular,
--   $$\Pr(N_x=k)=kx^2(1-x)^{k-1}\quad(k\ge1),\qquad\mathbb E[\log N_{T_u}]=C.$$
--   The full geometric joint law, integrability and almost sure success of the extended runs accompany this reference-cost identity.
--
--   Differences from the source:
--   - encoding: Conditional priorities and positive geometric variables → Update the coordinate priority to x in the product law; geometric variables are first-mark distances; reason: This is the regular conditional experiment; sentinels use integers and infinite unmarked runs are a null event.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 3, PDF p. 4, Lemma 3; continuation p. 4, PDF p. 5

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_3 {n : ℕ} (I : StableMatching.Instance n)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (u : Fin n) :
    (∀ P : Finset (Fin n), u ∉ P →
      (∀ ν : StableMatching.Matching n, I.IsStable ν → (∀ p ∈ P, ν p = μ p) →
        leftBoundary I μ u P < (idx I ν u : ℤ) ∧ (idx I ν u : ℤ) < rightBoundary I μ u P) ∧
      (supportSize I μ u P : ℤ) ≤ rightBoundary I μ u P-leftBoundary I μ u P-1) ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      (∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        revealLaw n {t | firstMark I μ u .left (Function.update t (.inl u) x) = a ∧
          firstMark I μ u .right (Function.update t (.inl u) x) = b} =
          ENNReal.ofReal (x^2*(1-x)^(a+b-2))) ∧
      (∀ k : ℕ, 1 ≤ k →
        revealLaw n {t | firstMark I μ u .left (Function.update t (.inl u) x) +
          firstMark I μ u .right (Function.update t (.inl u) x)-1 = k} =
          ENNReal.ofReal ((k : ℝ)*x^2*(1-x)^(k-1))) ∧
      (∀ k : ℕ,
        revealLaw n {t | (k : ℤ) ≤ rightBoundary I μ u (predecessors u (Function.update t (.inl u) x)) -
          leftBoundary I μ u (predecessors u (Function.update t (.inl u) x))-1} ≤
        revealLaw n {t | k ≤ firstMark I μ u .left (Function.update t (.inl u) x) +
          firstMark I μ u .right (Function.update t (.inl u) x)-1})) ∧
    (∀ᵐ t ∂revealLaw n, Good I μ u t) ∧
    MeasureTheory.Integrable (fun t => Real.log ((firstMark I μ u .left t : ℝ) + firstMark I μ u .right t-1)) (revealLaw n) ∧
    expected (fun t => Real.log ((firstMark I μ u .left t : ℝ) + firstMark I μ u .right t-1)) = C := by sorry

end SwitchingStable.Universal
