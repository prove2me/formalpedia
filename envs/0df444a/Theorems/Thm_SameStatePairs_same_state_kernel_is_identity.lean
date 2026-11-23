-- Prove2me | Theorems.Thm_SameStatePairs_same_state_kernel_is_identity
-- name    : SameStatePairs.same_state_kernel_is_identity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T21:02:04.959792+00:00
-- url     : https://prove2.me/theorems/1dcd2776-d5ed-4e22-bb81-2136f89dec38
-- title:
--   Lemma 1: same-state pairs make the world kernel the identity
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$ and $\sum_zp(z)=1$, write $d_z=|Z|$, and take the same-state positive-pair law $\pi=\operatorname{diag}(p)$, with the hard-whitening population objective in dimension $k$. Then:
--
--   1. $K_\pi=I$ and $T_\pi=I$.
--   2. Every centred, whitened $h:Z\to\mathbb{R}^k$ has $\Omega(h)=0$ and prediction term $L_\pi(h)=0$.
--   3. Every eigenvalue of $K_\pi$ equals $1$.
--   4. If $1\le k<d_z-1$, every $k$-dimensional subspace $V$ of the centred state-function space $\{\varphi:Z\to\mathbb{R}:\ \mathbb{E}_p\varphi=0\}$ is the span of some global minimiser.
--   5. If $k=d_z-1$, every global minimiser spans the whole centred space, and any two global minimisers $h,h'$ satisfy $h'=Qh$ for some $Q\in O(k)$.
--   6. If $1\le k<d_z-1$, the uniqueness premise of Theorem 1 of Balestriero and LeCun fails: there are global minimisers $h,h'$ such that $h'\ne Qh$ for every $Q\in O(k)$.
--
--   Same-state pairs never join two different states, so the prediction term charges nothing for any function of the state.
--
--   **Formalization Note** The span of an encoder is the span of its coordinate functions $h_1,\dots,h_k$. The uniqueness premise is stated as: for all global minimisers $h,h'$ there is $Q\in O(k)$ with $h'(z)=Qh(z)$ for all $z$.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 2.1, Lemma 1, p. 3

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem same_state_kernel_is_identity {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1) :
    worldKernel p (sameStateLaw p) = 1 ∧ markovOp p (sameStateLaw p) = 1 ∧
    (∀ h : Z → Fin k → ℝ, IsCentered p h → IsWhitened p h →
      hardOmega p h = 0 ∧ pairLoss (sameStateLaw p) h = 0) ∧
    (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (worldKernel p (sameStateLaw p))) μ →
      μ = 1) ∧
    (1 ≤ k → k + 1 < Fintype.card Z →
      ∀ V : Submodule ℝ (Z → ℝ), V ≤ centeredSpace p → Module.finrank ℝ V = k →
        ∃ h : Z → Fin k → ℝ, IsGlobalMin p (sameStateLaw p) h ∧ coordSpan h = V) ∧
    (k + 1 = Fintype.card Z →
      (∀ h : Z → Fin k → ℝ, IsGlobalMin p (sameStateLaw p) h → coordSpan h = centeredSpace p) ∧
      (∀ h h' : Z → Fin k → ℝ, IsGlobalMin p (sameStateLaw p) h →
        IsGlobalMin p (sameStateLaw p) h' →
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h' z = rot Q (h z))) ∧
    (1 ≤ k → k + 1 < Fintype.card Z →
      ¬ ∀ h h' : Z → Fin k → ℝ, IsGlobalMin p (sameStateLaw p) h →
        IsGlobalMin p (sameStateLaw p) h' →
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h' z = rot Q (h z)) := by sorry

end SameStatePairs
