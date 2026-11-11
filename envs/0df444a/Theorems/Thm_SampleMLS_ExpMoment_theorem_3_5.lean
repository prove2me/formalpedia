-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_theorem_3_5
-- name    : SampleMLS.ExpMoment.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:51:38.316751+00:00
-- url     : https://prove2.me/theorems/04d8e50a-af8b-4d8d-9884-97f3af569fbe
-- title:
--   Theorem 3.5 (Exponential-moment Monotone Local Search) — MLS-θ runs in time 2^{ψn}N^{O(1)} and space N^{O(1)} plus that of A, with one-sided error e^{−κ} under (⋆)
-- statement:
--   Let $\Phi=(U,F)$ be an implicit set system, and let the deterministic algorithm $A$ solve Φ-Extension with running-time exponent $g$. Let $\psi\ge0$, $\Gamma\ge1$, $\kappa>0$ be real numbers that are computed from $(I,k)$ in time $N^{O(1)}$ (to any precision $2^{-j}$ in time $(N+j+2)^{O(1)}$) and whose values are at most $N^{O(1)}$. Let the cap $\Theta(I,k)$ and the trial counts $m_{t,\theta}(I,k)$ be any ones satisfying (2) for every $I$ and $k\le n$, computed in time $N^{O(1)}$.
--
--   Then there are one constant $c$ and one program $P$ on the randomized log-cost RAM, implementing Algorithm MLS-θ$(\psi,\Gamma,\kappa)$ and calling $A$ as a subroutine, such that for every instance $I$ (with $N=|I|$, $n=|U_I|$) and every $k\le n$, on input $(I,k)$:
--
--   - the law of $P$'s answer is the law of Algorithm 3.4 (the trial loop, with $A$'s answers on the samples), and $P$ answers yes or no on every branch;
--   - every call of $A$ that $P$ makes is on an input $(I,X,k)$ with $X\subseteq U_I$ and $|X|\le k$ (so "the space of $A$" is its space on the extension calls of Algorithm 3.4);
--   - (i) $P$ runs in time $2^{\psi n}(N+2)^c$, counting its own log-cost and the running time of every call of $A$, and halts on every branch within that time; its own space is at most $(N+2)^c$, so that it runs in space $N^{O(1)}$ plus the space of $A$;
--   - (ii) if $F_I$ contains no set of size at most $k$, $P$ answers no on every outcome of its coins;
--   - (iii) if $F_I$ contains a set $S$ with $|S|=k$ that satisfies (⋆) $\max_{0\le t\le k}\mu_t(S)/\binom{n}{t}\ge2^{-\psi n}/\Gamma$, $P$ answers yes with probability at least $1-e^{-\kappa}$;
--   - condition (⋆) holds for such an $S$ if $W_S(y)\ge(1+y)^n2^{-\psi n}/\Gamma$ for some $y\ge0$.
--
--   Differences from the source:
--   - encoding: an unnamed machine; time up to N^{O(1)} factors; "the space of A" → the published randomized log-cost RAM PDSEquiv.Machine; MLS-θ is an oracle program whose oracle returns A's output; its time is its own log-cost plus runTime of A on each call (CompositeTimeWithin); its own space (runSpace) is bounded, every call of A is on some (I, X, k) with X ⊆ U_I, |X| ≤ k (QueriesSatisfy), and the composite space is that plus the space of A on those calls; reason: the page assumes exact uniform draws in polynomial time (exact Ber(a/b) gives them) and counts A's time per call and A's space once, as a subroutine
--   - encoding: instances I ∈ {0,1}*, N = |I|, a universe U_I listed in polynomial time; N^{O(1)} → I : List Bool; U_I : Finset ℕ (element codes); (N + 2)^c with one c chosen before I and k; reason: the same instances; + 2 keeps the bound positive at N ≤ 1
--   - reading: Algorithm MLS-θ(ψ, Γ, κ) runs / answers … → ∃ c, ∃ P (one program) such that for every I and k ≤ n the law of P's answer equals mlsLaw, the law of the trial loop of Algorithm 3.4 with A's answers, and (i)–(iii) hold for P; reason: Algorithm 3.4 is pseudocode; a statement about its running time is a statement about an implementation of it, and the law clause ties P to the algorithm
--   - reading: A is an algorithm solving Φ-Extension → A is a deterministic program (no Bernoulli draws, no oracle calls) that halts on every input (I, X, k), X ⊆ U_I, with the correct answer; reason: Corollary 3.15 (p. 23) treats randomized extension algorithms separately, with Γ replaced by 2Γ, so the A of Theorem 3.5 is deterministic
--   - reading: ψ, Γ, κ "can be computed from (I, k) in time N^{O(1)}" (real numbers) → PolyApproximable: one deterministic program outputs a rational within 2^{−j} of the value on (I, k, j) in time (N + j + 2)^c; reason: the standard meaning of computing a real number; rational parameters computed exactly qualify
--   - reading: "with any cap Θ and trial counts m_{t,θ} satisfying (2)" → any functions Θ(I, k) : ℤ and m_{t,θ}(I, k) : ℕ satisfying (2) for every I and k ≤ n, each computed by a deterministic program in time (N + 2)^{c}; c in the conclusion may depend on these programs; reason: the algorithm must compute its parameters; the page notes integers in these ranges are computable in time N^{O(1)} (p. 16)
--   - generalization: g(I, X, k) can be computed in time N^{O(1)}; comparisons with integer or rational thresholds of polynomial bit length are decided in time N^{O(1)} (p. 15) → one deterministic program decides g(I, X, k) ≤ θ for integer thresholds 0 ≤ θ ≤ (N + 2)^a, in time (N + 2)^{c(a)} for each a; reason: the page's hypothesis implies this one (such θ have polynomial bit length) and the algorithm compares only with θ ∈ {0, …, Θ}; the Lean admits more exponents g
--   - encoding: ψ ≥ 0, Γ ≥ 1, κ > 0, the value bounds, (2): stated for the inputs (I, k) of the algorithm → the same hypotheses for every I and k ≤ n; reason: the algorithm is only given k ≤ n
--   - encoding: (ii) "answers no" on a no-instance → on every halted branch the output is [0] (OutputsSatisfy), with halting on every branch from (i); reason: the every-outcome form of one-sided error (p. 14)
--   - encoding: integer trial counts → m : … → ℕ; reason: (2) forces m_{t,θ} ≥ M_{t,θ} > 0
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), Theorem 3.5, pp. 16–17 (PDF 18–19); Algorithm 3.4, p. 16 (PDF 18); proof pp. 18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Theorem 3.5 (Exponential-moment Monotone Local Search), pp. 16–17 (PDF 18–19). For an implicit
set system `Φ = (U, F)`, a deterministic algorithm `A` solving Φ-Extension with running-time
exponent `g`, parameters `ψ ≥ 0`, `Γ ≥ 1`, `κ > 0` computed from `(I, k)` in polynomial time with
values at most `N^{O(1)}`, and any cap `Θ` and trial counts `m_{t,θ}` satisfying (2) (computed in
polynomial time): there is one constant `c` and one program `P` implementing Algorithm MLS-θ, calling
`A` as a subroutine, such that on every `I` and `k ≤ n` the law of its answer is the law of
Algorithm 3.4, every call of `A` is on an input `(I, X, k)` with `X ⊆ U_I` and `|X| ≤ k`, and (i) it runs in time `2^{ψn}(N + 2)^c` (its own cost plus that of the calls of
`A`) and in space `(N + 2)^c` besides the space of `A`; (ii) it answers no on every outcome if
`F_I` has no set of size at most `k`; (iii) it answers yes with probability at least `1 − e^{−κ}` if
some `S ∈ F_I` with `|S| = k` satisfies (⋆); and (⋆) holds if
`W_S(y) ≥ (1 + y)^n 2^{−ψn}/Γ` for some `y ≥ 0`. -/
theorem theorem_3_5
    (U : List Bool → Finset ℕ) (F : List Bool → Set (Finset ℕ)) (hΦ : IsImplicitSetSystem U F)
    (A : PDSEquiv.Program) (hA : SolvesExtension U F A)
    (g : List Bool → Finset ℕ → ℕ → ℝ) (hg : IsRunningTimeExponent U A g)
    (ψ Γ κ : List Bool → ℕ → ℝ)
    (hψ : ∀ I k, k ≤ (U I).card → 0 ≤ ψ I k) (hΓ : ∀ I k, k ≤ (U I).card → 1 ≤ Γ I k)
    (hκ : ∀ I k, k ≤ (U I).card → 0 < κ I k)
    (hψc : PolyApproximable U ψ) (hΓc : PolyApproximable U Γ) (hκc : PolyApproximable U κ)
    (hval : ∃ c : ℕ, ∀ I k, k ≤ (U I).card →
      ψ I k ≤ ((I.length : ℝ) + 2) ^ c ∧ Γ I k ≤ ((I.length : ℝ) + 2) ^ c ∧
      κ I k ≤ ((I.length : ℝ) + 2) ^ c)
    (Θ : List Bool → ℕ → ℤ) (m : List Bool → ℕ → ℕ → ℤ → ℕ)
    (hΘc : ∃ (R : PDSEquiv.Program) (c : ℕ), ∀ I k, k ≤ (U I).card →
      DetComputes R (encIk I k) (((I.length + 2) ^ c : ℕ) : ℝ≥0∞) (fun o => o = encInt (Θ I k)))
    (hmc : ∃ (R : PDSEquiv.Program) (c : ℕ), ∀ I k, k ≤ (U I).card → ∀ t ≤ k, ∀ θ : ℕ,
      (θ : ℤ) ≤ Θ I k →
        DetComputes R (encIk I k ++ [t, θ]) (((I.length + 2) ^ c : ℕ) : ℝ≥0∞)
          (fun o => o = encInt (m I k t θ)))
    (h2 : ∀ I k, k ≤ (U I).card →
      Cond2 (ψ I k) (Γ I k) (κ I k) (U I).card k (Θ I k) (m I k)) :
    ∃ c : ℕ, ∃ P : PDSEquiv.Program, ∀ (I : List Bool) (k : ℕ), k ≤ (U I).card →
      PDSEquiv.outMass P (subOracle A) (encIk I k) yesOut =
        (mlsLaw (U I) (fun X => g I X k) (fun X => detOut A (encIXk I X k) = yesOut) k
          (Θ I k) (m I k) true).toReal ∧
      PDSEquiv.outMass P (subOracle A) (encIk I k) noOut =
        (mlsLaw (U I) (fun X => g I X k) (fun X => detOut A (encIXk I X k) = yesOut) k
          (Θ I k) (m I k) false).toReal ∧
      PDSEquiv.OutputsSatisfy P (subOracle A) (encIk I k) (fun o => o = yesOut ∨ o = noOut) ∧
      PDSEquiv.QueriesSatisfy P (subOracle A) (encIk I k)
        (fun q => ∃ X ⊆ U I, X.card ≤ k ∧ q = encIXk I X k) ∧
      CompositeTimeWithin P A (encIk I k)
        ((2 : ℝ) ^ (ψ I k * ((U I).card : ℝ)) * ((I.length : ℝ) + 2) ^ c) ∧
      runSpace P (subOracle A) (encIk I k) ≤ (((I.length + 2) ^ c : ℕ) : ℝ≥0∞) ∧
      ((¬ ∃ S ∈ F I, S.card ≤ k) →
        PDSEquiv.OutputsSatisfy P (subOracle A) (encIk I k) (fun o => o = noOut)) ∧
      (∀ S ∈ F I, S.card = k → Star (fun X => g I X k) (U I) S (ψ I k) (Γ I k) →
        1 - Real.exp (-(κ I k)) ≤ PDSEquiv.outMass P (subOracle A) (encIk I k) yesOut) ∧
      (∀ S ∈ F I, S.card = k → ∀ y : ℝ, 0 ≤ y →
        (1 + y) ^ (U I).card * (2 : ℝ) ^ (-(ψ I k * ((U I).card : ℝ))) / Γ I k ≤
          W (fun X => g I X k) S y →
        Star (fun X => g I X k) (U I) S (ψ I k) (Γ I k)) := by sorry

end SampleMLS.ExpMoment
