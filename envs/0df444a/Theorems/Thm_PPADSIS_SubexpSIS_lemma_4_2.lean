-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_lemma_4_2
-- name    : PPADSIS.SubexpSIS.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:49:00.268622+00:00
-- url     : https://prove2.me/theorems/92359d21-0f0f-491b-adbd-ebdbbbacde69
-- title:
--   Lemma 4.2 — from state uniqueness to τ-bounded soundness, with overhead (τ + 2)·poly(λ, N)
-- statement:
--   Let $U$ be a uuSNARG (syntax, completeness and succinctness of Definition 4.1). There is a polynomial $\mathrm{poly}(\lambda,N)$, depending only on $U$, such that the following holds. Let $N$ be a polynomial, let $\tau=\tau(\lambda)$ be a time bound, and let $A$ be an adversary of size $s(\lambda)$ that outputs either $\bot$ or a triple whose time satisfies $t\le\tau$. Suppose that, at some $\lambda$,
--   $$\Pr\left[\begin{array}{l}p\le H\wedge|C|\le N(\lambda)\wedge t\in[0,P]\\ \wedge\ \mathrm{Verify}(\mathrm{crs},\mathrm{pp},t,\mathrm{st})=1\wedge\mathrm{st}\ne\mathrm{st}_t\end{array} : \begin{array}{l}\mathrm{crs}\leftarrow\mathrm{Setup}(1^\lambda,1^{N(\lambda)}),\ (C,t,\mathrm{st})\leftarrow A(\mathrm{crs})\\ \mathrm{pp}:=\mathrm{Preprocess}(\mathrm{crs},C),\ \mathrm{st}_t:=\mathrm{Update}^t(\mathrm{Initialize}(\mathrm{crs},\mathrm{pp}))\end{array}\right]\ge\epsilon(\lambda).$$
--   Then there is an adversary of size $s(\lambda)+(\tau+2)\cdot\mathrm{poly}(\lambda,N(\lambda))$ that breaks state uniqueness (Definition 4.1) for the size bound $N$ with probability at least $\epsilon(\lambda)$.
--
--   The lemma turns state uniqueness, a collision-style property, into soundness against a single wrong accepted state, at the price of recomputing the honest state; Theorem 4.7 uses it with $\tau=2^H$, which is why it needs state uniqueness against adversaries of exponential size.
--
--   Differences from the source:
--   - reading: "Let U be a uuSNARG" (implicit in the lemma) → `IsUUSNARG`: the syntax with an admissible height bound, completeness and succinctness, without state uniqueness; reason: the proof uses completeness and succinctness, and Theorems 4.5 and 4.7 assume state uniqueness separately.
--   - reading: "poly(λ, N(λ))" → $(\lambda+N(\lambda)+2)^k$ with $k$ chosen before $N,\tau,s,\epsilon,A$; reason: the overhead is a polynomial in $\lambda$ and the value $N(\lambda)$ that depends only on $U$.
--   - encoding: the hypothesis and conclusion at each $\lambda$ (`∀ λ, Pr ≥ ε(λ) → ∃ A′ …` with $A'$'s size bounded at that $\lambda$); reason: the lemma is a per-$\lambda$ reduction.
--   - encoding: adversary outputs as codes (`encTriple`, `encQuad`), $\bot$ as the empty output or a failed run, "a triple whose time satisfies $t\le\tau$" required on every crs in Setup's support; the event requires $C$ to be a well-formed regular tree circuit; reason: Lean representation of the experiments of Definition 4.1 and Lemma 4.2.
--   - encoding: "Let N be a polynomial" → $N\in\mathbb N[X]$; reason: polynomials with natural coefficients represent the paper's polynomial size bounds.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 25, Lemma 4.2

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_UUSNARG

namespace PPADSIS.SubexpSIS

open Polynomial

theorem lemma_4_2 (U : UUSNARG) (hU : U.IsUUSNARG) :
    ∃ k : ℕ, ∀ (N : ℕ[X]) (τ : ℕ → ℕ) (s : ℕ → ℝ) (ε : ℕ → ℝ) (A : Adversary),
      A.SizeLE s → U.BotOrTimeBounded N τ A → ∀ lam : ℕ, U.soundAdv N A lam ≥ ε lam →
        ∃ A' : Adversary,
          A'.SizeAtMost lam (s lam + ((τ lam : ℝ) + 2) * ((lam : ℝ) + N.eval lam + 2) ^ k) ∧
          U.uniqAdv N A' lam ≥ ε lam := by sorry

end PPADSIS.SubexpSIS
