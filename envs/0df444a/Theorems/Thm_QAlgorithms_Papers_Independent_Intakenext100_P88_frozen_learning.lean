-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_frozen_learning
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.frozen_learning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:27:31.436309+00:00
-- url     : https://prove2.me/theorems/1ac6a0e9-50cb-45e9-b3f0-b66a36bf2b05
-- title:
--   Frozen learning: finite dynamics, asymptotic prediction and norm-log rate
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   Absorb the reference angles into the fixed gates and set $\theta=\delta\varphi$, where $\delta>0$. Write $J_{a\ell}=\partial_{\varphi_\ell}z_a(0)$ and $H_{a,k\ell}=\partial_{\varphi_k}\partial_{\varphi_\ell}z_a(0)$ for derivatives of the actual circuit. The frozen kernel is $K_{ab}=\sum_\ell J_{a\ell}J_{b\ell}$.
--
--   Let $A$ and $I$ be nonempty finite training and observable index sets. Put $K_A=K|_{(A\times I)^2}$, let $z^0$ be the first Taylor output at initial rescaled angles $v$, and set $e_a=z^0_a-y_a$ on training indices. Assume $\det K_A\ne0$, $\eta>0$, $1-\eta K_A\succ0$, and $\|1-\eta K_A\|_2<1$. Equivalently, all eigenvalues obey $0<1-\eta\lambda<1$, the positive-step geometric-series and real-log regime used in the source. Under the frozen recurrences, for every $t\in\mathbb N$ and general data-observable index $a$,
--   $$
--   \epsilon(t)=(1-\eta K_A)^t e\longrightarrow0,\qquad
--   z_a(t)\longrightarrow z^0_a-\sum_{b,c\in A\times I}K_{ab}(K_A^{-1})_{bc}e_c.
--   $$
--   On training indices $z_a(t)-y_a\to0$. The paper's statistic $\tau_c(s)=\|{-\log(1-sK_A)}\|_2$ satisfies $\lim_{s\downarrow0}\tau_c(s)/s=\|K_A\|_2$. This packages the finite solution, training interpolation, and prediction on general data. The norm is the L2 operator norm, and the inverse is solely the restricted training inverse.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 6, Main Theorem 3; SM Eqs.(98)-(104)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.6 Theorem 3, SM pp.24-25 Eqs.(98)-(104): frozen finite-time solution,
asymptotic prediction and training interpolation. The inverse is only the training kernel.
Positive definiteness of I-eta K and its strict L2 contraction make the proof's positive
geometric-series/logarithm regime explicit. The norm-log approximation is its one-sided
small-learning-rate leading term; it is not the slowest-mode rate. -/
theorem frozen_learning {D T I : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype I] [DecidableEq I] [Nonempty I] {h L : ℕ}
    (M : ExpectationNetwork D I h L) (embed : T ↪ D)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (y : T × I → ℝ)
    (hinv : (trainingKernel M delta embed).det ≠ 0)
    (hpositive : (1 - eta • trainingKernel M delta embed).PosDef)
    (hcontract : QAlgorithms.specNorm (1 - eta • trainingKernel M delta embed) < 1) :
    let K := trainingKernel M delta embed
    let z := linearOutput M delta v
    let e : EuclideanSpace ℝ (T × I) := WithLp.toLp 2
      (fun a => z (trainingIndex embed a) - y a)
    let Z := prediction (frozenKernel M delta) (trainingIndex embed) eta z e
    (∀ t, frozenResidual K eta e t = l2Action ((1 - eta • K) ^ t) e) ∧
    Tendsto (frozenResidual K eta e) atTop (nhds 0) ∧
    (∀ a, Tendsto (fun t => Z t a) atTop
      (nhds (z a - ∑ b, ∑ c, frozenKernel M delta a (trainingIndex embed b) *
        (K⁻¹) b c * e c))) ∧
    (∀ a, Tendsto (fun t => Z t (trainingIndex embed a) - y a) atTop (nhds 0)) ∧
    Tendsto (fun s : ℝ => logRate K s / s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (QAlgorithms.specNorm K)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
