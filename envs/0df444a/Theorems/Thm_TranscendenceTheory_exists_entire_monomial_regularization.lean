-- Prove2me | Theorems.Thm_TranscendenceTheory_exists_entire_monomial_regularization
-- name    : TranscendenceTheory.exists_entire_monomial_regularization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T13:36:58.746908+00:00
-- url     : https://prove2.me/theorems/f524030e-e457-4d53-9e3a-27c19a577c1f
-- title:
--   Entire extension and growth bound for finite sums with weighted poles
-- statement:
--   Let $I,J$ be finite index sets, $U\subseteq\mathbb C$, and let $\sigma$ and $\psi_j$ be entire functions. Let $\phi_j:\mathbb C\to\mathbb C$ be arbitrary functions and $w_j\ge1$ integers such that
--
--   $$\psi_j(z)=\sigma(z)^{w_j}\phi_j(z)\qquad(z\in U).$$
--
--   Fix $v\in\mathbb C$, coefficients $c_i\in\mathbb C$, and nonnegative integers $\ell_i,e_{ij},D,K$ satisfying
--
--   $$\ell_i\le D,\qquad \sum_j w_je_{ij}\le K\qquad(i\in I).$$
--
--   There exists an entire function $G$, independent of the bounds below, such that
--
--   $$G(z)=\sigma(z)^K\sum_i c_i(z+v)^{\ell_i}\prod_j\phi_j(z)^{e_{ij}}\qquad(z\in U).$$
--
--   For every pair of real numbers $R,B$ with $B\ge1$, if $|\sigma(z)|\le B$ and $|\psi_j(z)|\le B$ for all $j$ and all $|z|\le R$, then
--
--   $$|G(z)|\le\left(\sum_i|c_i|\right)\max(1,R+|v|)^D B^K\qquad(|z|\le R).$$
--
--   Empty index sets, zero coefficients, $K=0$, and zeros of $\sigma$ are allowed. Equality with the original expression is only asserted on $U$; the entire extension has its own values elsewhere. For the elliptic application the weights of $\zeta,\wp,\wp'$ are $1,2,3$. This is a supporting finite-sum formulation of the construction and growth argument in Lemma 6, rather than a claim that the source states this general theorem.
-- source:
--   Supporting generalization of the monomial pole-clearing and growth argument in Senthil Kumar K (2026), Section 4, proof of Lemma 6(i)-(ii), especially equation (16) and the preceding entire sigma factors. Basic entire factors are explicit hypotheses; the theorem does not construct the Weierstrass sigma function. https://doi.org/10.1017/S001309152610145X

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

open Finset Set

theorem TranscendenceTheory.exists_entire_monomial_regularization
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (U : Set ℂ) (σ : ℂ → ℂ) (φ ψ : κ → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ)
    (hψ : ∀ j, AnalyticOnNhd ℂ (ψ j) univ)
    (w : κ → ℕ) (hw : ∀ j, 1 ≤ w j)
    (hrel : ∀ z ∈ U, ∀ j, ψ j z = σ z ^ w j * φ j z)
    (v : ℂ) (c : ι → ℂ) (l : ι → ℕ) (e : ι → κ → ℕ)
    (D K : ℕ) (hl : ∀ i, l i ≤ D) (he : ∀ i, ∑ j, w j * e i j ≤ K) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z ∈ U, G z = σ z ^ K * ∑ i, c i * (z + v) ^ l i * ∏ j, φ j z ^ e i j) ∧
      ∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖ψ j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K := by sorry
