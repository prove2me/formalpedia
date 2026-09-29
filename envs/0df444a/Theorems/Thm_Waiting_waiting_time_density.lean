-- Prove2me | Theorems.Thm_Waiting_waiting_time_density
-- name    : Waiting.waiting_time_density
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T17:48:19.690735+00:00
-- url     : https://prove2.me/theorems/e36c52b6-06fb-4904-86f7-1129abeab6c4
-- title:
--   Siegel Theorem 2.2: density of the order-statistic waiting time
-- statement:
--   Siegel 2001, Theorem 2.2 / §2.1.1: the waiting-time CDF density (t-domain bridge). For $N$ independent rate-$\lambda$ exponential switches, the waiting time $T$ to reach $m+1$ has CDF $F(t)=\sum_{k=m+1}^{N}\binom{N}{k}(1-e^{-\lambda t})^k(e^{-\lambda t})^{N-k}$ (the binomial upper tail with $p$ replaced by $q(t)=1-e^{-\lambda t}$). By the chain rule its density is $F'(t)=N\binom{N-1}{m}(1-e^{-\lambda t})^m(e^{-\lambda t})^{N-m}\lambda$. Equivalently (since $N\binom{N-1}{m}=\binom{N}{m}(N-m)$) this is Siegel's $f(t)=\binom{N}{np-1}(1-e^{-\lambda t})^{np-1}e^{-\lambda t(N+1-np)}\lambda(N+1-np)$ with $np=m+1$. This is the t-domain bridge feeding Lemma 2.1 and Theorem 2.1 toward the integer-mean binomial median.
-- source:
--   A. Siegel, "Median Bounds and their Application", Journal of Algorithms 38 (2001) 184-236, Theorem 2.2 / §2.1.1, p.6 (waiting-time CDF F(t) and density f(t)). Proven by composing the FTC binomial-tail derivative (already proved on platform as binomial_upper_tail_eq_incomplete_beta, id 920fcc62) with the substitution q(t)=1-exp(-lambda*t) via the chain rule.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Waiting

/-- One binomial-tail term, as a function of `p`. -/
noncomputable def binTerm (N k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)

/-- `Aterm k(x) = N·C(N-1,k-1)·x^{k-1}·(1-x)^{N-k}` (Siegel §2.1.1 telescoping term). -/
noncomputable def Aterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) * x ^ (k-1) * (1 - x) ^ (N - k)
noncomputable def Bterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) k : ℝ) * x ^ k * (1 - x) ^ (N - 1 - k)

theorem term_deriv (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (Aterm N k x - Bterm N k x) x := by
  have h1 : HasDerivAt (fun p : ℝ => p ^ k) ((k : ℝ) * x ^ (k-1)) x := by
    simpa using hasDerivAt_pow k x
  have h2 : HasDerivAt (fun p : ℝ => (1 - p) ^ (N-k)) (-(((N-k : ℕ) : ℝ) * (1-x)^(N-k-1))) x := by
    have hb : HasDerivAt (fun p : ℝ => (1 - p)) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have := hb.fun_pow (N-k)
    have e : -(((N-k : ℕ) : ℝ) * (1-x)^(N-k-1)) = ((N-k : ℕ) : ℝ) * (1-x)^(N-k-1) * (-1) := by ring
    rw [e]; exact this
  have hmul : HasDerivAt (fun p : ℝ => p ^ k * (1 - p) ^ (N-k))
      ((k : ℝ) * x ^ (k-1) * (1-x)^(N-k) + x^k * (-(((N-k:ℕ):ℝ) * (1-x)^(N-k-1)))) x := h1.mul h2
  have hp := hmul.const_mul (Nat.choose N k : ℝ)
  have hfun : (fun p : ℝ => (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)))
      = (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
    funext p; ring
  rw [hfun] at hp
  have e1 : (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) = (Nat.choose N k : ℝ) * (k : ℝ) := by
    have := Nat.add_one_mul_choose_eq (N-1) (k-1)
    have hk : (k-1)+1 = k := by omega
    have hN' : (N-1)+1 = N := by omega
    rw [hk, hN'] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    linarith [this]
  have e2 : (N : ℝ) * (Nat.choose (N-1) k : ℝ) = (Nat.choose N k : ℝ) * ((N - k : ℕ) : ℝ) := by
    have := Nat.choose_mul_succ_eq (N-1) k
    have hN' : (N-1)+1 = N := by omega
    rw [hN'] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    linarith [this]
  have he : N - 1 - k = N - k - 1 := by omega
  have hval : Aterm N k x - Bterm N k x
      = (Nat.choose N k : ℝ) * ((k : ℝ) * x ^ (k-1) * (1-x)^(N-k) + x^k * (-(((N-k:ℕ):ℝ) * (1-x)^(N-k-1)))) := by
    simp only [Aterm, Bterm, he]
    rw [e1, e2]
    ring
  rw [hval]; exact hp

theorem Bterm_eq_Aterm_succ (N k : ℕ) (x : ℝ) : Bterm N k x = Aterm N (k+1) x := by
  unfold Aterm Bterm
  have h1 : k + 1 - 1 = k := by omega
  rw [h1]; congr 2; omega

theorem Aterm_top_zero (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : Aterm N (N+1) x = 0 := by
  unfold Aterm
  have hz : Nat.choose (N-1) (N+1-1) = 0 := by
    apply Nat.choose_eq_zero_of_lt; omega
  rw [hz]; simp

/-- Derivative of the binomial UPPER tail in `p`: telescopes to a single term. -/
theorem tail_deriv (N m : ℕ) (h : m < N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m)) x := by
  have hsum : HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Bterm N k x)) x := by
    have hh := HasDerivAt.sum (u := Finset.Ico (m+1) (N+1))
      (A := fun k => fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (A' := fun k => Aterm N k x - Bterm N k x) (x := x)
      (fun k hk => by rw [Finset.mem_Ico] at hk; exact term_deriv N k (by omega) (by omega) x)
    have hfe : (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
        = (∑ k ∈ Finset.Ico (m+1) (N+1), fun p : ℝ =>
            (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
      funext p; simp only [Finset.sum_apply]
    rw [hfe]; exact hh
  have htel : (∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Bterm N k x))
      = (N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m) := by
    have hstep : (∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Bterm N k x))
        = ∑ k ∈ Finset.Ico (m+1) (N+1), (Aterm N k x - Aterm N (k+1) x) := by
      apply Finset.sum_congr rfl; intro k _; rw [Bterm_eq_Aterm_succ]
    rw [hstep, Finset.sum_Ico_eq_sum_range]
    have hlen : N + 1 - (m + 1) = N - m := by omega
    rw [hlen]
    have hcongr : (∑ i ∈ Finset.range (N-m), (Aterm N (m+1+i) x - Aterm N (m+1+i+1) x))
        = ∑ i ∈ Finset.range (N-m), ((fun j => Aterm N (m+1+j) x) i - (fun j => Aterm N (m+1+j) x) (i+1)) := by
      apply Finset.sum_congr rfl; intro i _; simp only []; ring_nf
    rw [hcongr, Finset.sum_range_sub' (fun j => Aterm N (m+1+j) x) (N-m)]
    have hb : m + 1 + (N - m) = N + 1 := by omega
    rw [hb, Aterm_top_zero N (by omega)]
    simp only [sub_zero]
    unfold Aterm
    rw [show m+1-1 = m from by omega, show N - (m+1) = N - 1 - m from by omega]
  rw [← htel]; exact hsum

theorem waiting_time_density (N m : ℕ) (lam : ℝ) (h : m < N) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * t))) ^ m
          * (Real.exp (-(lam * t))) ^ (N - m) * lam) t := by sorry
