-- Prove2me | Theorems.Thm_ProcessingNetworks_DTMCFoster_lemma_C_23
-- name    : ProcessingNetworks.DTMCFoster.lemma_C_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:26:37.062017+00:00
-- url     : https://prove2.me/theorems/403b4f66-fd48-47a3-938f-4987bce4b8f2
-- title:
--   Lemma C.23 — finite expected return times to a finite set imply positive recurrence (corrected: C nonempty)
-- statement:
--   Let $X$ be an irreducible discrete-time Markov chain on a countable state space $\mathcal S$ with transition matrix $P$. Let $C\subseteq\mathcal S$ be a **nonempty** finite set and let
--   $$
--   T_C=\inf\{k\ge1 : X_k\in C\}
--   $$
--   be the first passage time of $X$ into $C$ (eq. (C.16)). Suppose that
--   $$
--   \mathbb E_x\big(T_C\big)<\infty\qquad\text{for each } x\in C. \tag{C.17}
--   $$
--   Then:
--   1. $X$ is positive recurrent: $\mathbb E_i(\tau_i)<\infty$ for every state $i\in\mathcal S$, where $\tau_i=\inf\{k\ge1:X_k=i\}$;
--   2. $X$ has a unique stationary distribution, i.e. there is exactly one probability distribution $\pi$ on $\mathcal S$ with $\pi(i)=\sum_{j\in\mathcal S}\pi(j)P_{ji}$ for all $i$.
--
--   This reduces positive recurrence on an infinite state space to finiteness of the expected return times to a single finite set, which is the form in which the Foster–Lyapunov criteria (Theorems C.26 and C.27) are proved.
--
--   **Formalization Note** The chain is its transition matrix $P:S\to\mathrm{PMF}(S)$; $\mathbb E_x(T_C)$ is the tail sum $\sum_{n\ge0}\mathbb P_x(X_1\notin C,\dots,X_n\notin C)\in[0,\infty]$.
--
--   Differences from the source:
--   - correction: C ⊂ 𝒮 a finite subset → C finite and nonempty; reason: for C = ∅ condition (C.17) is vacuous, and the simple symmetric random walk on ℤ is irreducible and null recurrent, so the printed conclusion fails; the proof's embedded chain X̄ lives on C and needs C ≠ ∅
--   - encoding: a DTMC X on a countable state space 𝒮 with transition matrix P → the transition matrix P : S → PMF S (Chain S) on a type S with [Countable S]; reason: the statement depends on X only through P (and the initial state); a countable type covers the book's finite or countable 𝒮 (p.275)
--   - encoding: E_x(T_C) < ∞ with T_C = inf{k ≥ 1 : X_k ∈ C} (C.16) → meanReturn P C x = Σ_n P_x(X_1 ∉ C, …, X_n ∉ C) < ∞; reason: tail-sum formula for E_x(T_C) in [0, ∞]; it is ∞ whenever T_C = ∞ with positive probability, as the book's E_x(T_C) is
--   - encoding: X is positive recurrent (Def C.16) → PositiveRecurrent P: meanReturn P {i} i = E_i(τ_i) < ∞ for every state i; reason: Def C.16 applied to every state; a finite mean return time already makes the state recurrent
--   - encoding: a unique stationary distribution π : 𝒮 → [0, 1] (Def C.17) → ∃! π : S → [0, ∞] with Σ_i π(i) = 1 and Σ_j π(j) P(j, i) = π(i) for all i (KellyRSN.PartialBalance.IsStationaryProb); reason: a function with total mass 1 takes values in [0, 1]; these are exactly the probability distributions invariant for P (C.9)
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability (pre-publication draft 2020-4-2, spnbook.org), Appendix C, §C.7, Lemma C.23 with (C.16)–(C.17), p.280 (PDF p.296); Definitions C.16–C.17, p.279 (PDF p.295)

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_KellyRSN_PartialBalance_IsStationaryProb

open scoped ENNReal
open KellyStochasticNetworks.MaxWeight

namespace ProcessingNetworks.DTMCFoster

/-- **Lemma C.23** (a finite set with integrable return times), Dai & Harrison, *Processing
Networks*, pre-publication draft 2020-4-2, spnbook.org, Appendix C, §C.7, p.280, PDF p.296:
"Let `X` be an irreducible DTMC on a countable state space `𝒮`. Let `C ⊂ 𝒮` be a finite subset
and define `T_C` as the first passage time of `X` into `C`, that is, `T_C := inf{k ≥ 1 : X_k ∈ C}`
(C.16). Suppose that `E_x(T_C) < ∞` for each `x ∈ C` (C.17). Then `X` is positive recurrent. As a
consequence, it has a unique stationary distribution."

Corrected: `C` is assumed **nonempty**. For `C = ∅`, (C.17) is vacuous and the printed conclusion
fails for the simple symmetric random walk on `ℤ` (irreducible and null recurrent).

**Formalization Note** The chain is its transition matrix `P : S → PMF S` (`Chain S`, Def C.1
(C.2)) on a countable type `S`. `Irreducible P` says every `j` is reached from every `i` in some
number `n ≥ 0` of steps (Defs C.4–C.6). `meanReturn P C x = Σₙ P_x(X₁ ∉ C, …, Xₙ ∉ C)` is
`E_x(T_C) ∈ [0, ∞]` with `T_C` from (C.16) (infinite when `C` is missed with positive probability).
`PositiveRecurrent P` says `E_i(τᵢ) < ∞` for every state `i` (Def C.16 at every state). A
stationary distribution (Def C.17) is a function `π : S → [0, ∞]` with `Σᵢ π(i) = 1` and
`Σⱼ π(j) P(j, i) = π(i)` for all `i` (C.9). -/
theorem lemma_C_23 {S : Type*} [Countable S] (P : Chain S) (hirr : Irreducible P)
    (C : Set S) (hCfin : C.Finite) (hCne : C.Nonempty)
    (hC : ∀ x ∈ C, meanReturn P C x < ∞) :
    PositiveRecurrent P ∧
      ∃! π : S → ℝ≥0∞, KellyRSN.PartialBalance.IsStationaryProb (fun i j => P i j) π := by sorry

end ProcessingNetworks.DTMCFoster
