-- Prove2me | Theorems.Thm_TriFormQ_lemma_12
-- name    : TriFormQ.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:50:49.201892+00:00
-- url     : https://prove2.me/theorems/852333e9-fb11-4751-8d71-7833d7b8e708
-- title:
--   Lemma 12 (Stage 1 prefilter): $\lceil\log_q(L/\varepsilon)/\rho\rceil$ queries keep $f$ and remove every $T^i$ with $\mathrm{AR}(f-T^i)>\rho$ (corrected: count of Fig. 8, true form survives)
-- statement:
--   Let $T^1,\dots,T^L$ be an explicitly given list of trilinear forms on $\mathbb F_q^n$, and let the hidden form be $f=T^k$, accessible only through its evaluation oracle. Let $\rho>0$ be an analytic-rank threshold and $\varepsilon\in(0,1)$ a failure parameter. There is a randomized quantum query algorithm, depending on the list, $\rho$ and $\varepsilon$ but not on $k$, which outputs a set $S\subseteq[L]$ of surviving indices such that for every $k$:
--
--   1. it makes at most
--   $$\Big\lceil \tfrac{1}{\rho}\log_q\tfrac{L}{\varepsilon}\Big\rceil$$
--   queries to the oracle of $T^k$;
--   2. with probability at least $1-\varepsilon$, every index $i$ with $T^i=T^k$ survives ($i\in S$), and every surviving index satisfies $\mathrm{AR}(T^k-T^i)\le\rho$.
--
--   This is the first stage of the main algorithm: it removes every candidate far from the hidden form in analytic rank, so that the second stage only has to deal with low-analytic-rank differences.
--
--   Differences from the source:
--   - correction: at most $O_q\big(\frac{\log L}{\rho}+\frac1\rho\log\frac1\varepsilon\big)$ queries → at most $\lceil\log_q(L/\varepsilon)/\rho\rceil$ queries, Fig. 8's $t=\frac1\rho\log_q(L/\varepsilon)$ rounded up; reason: with the survival clause the O-form is false for large $\rho$: $q=2$, $L=2$, $T^1-T^2=\sum_i x_iy_iz_i$ on $\mathbb F_2^n$ ($\mathrm{AR}=n\log_2(4/3)>\rho:=n/4$), $\varepsilon=1/3$, $n$ large allows fewer than one query, and a 0-query algorithm meets the two disjoint success events with total probability at most 1
--   - reading: (ii) every surviving $T^i$ satisfies $\mathrm{AR}(f-T^i)\le\rho$ → (ii) plus every index $i$ with $T^i=f$ survives; reason: the printed (ii) alone is satisfied by the empty output with 0 queries; Fig. 8 never eliminates $f$ ("The true form always survives", p.6) and Stage 2 needs it
--   - encoding: an analytic rank bound $\rho$ → $0<\rho$; reason: the printed count contains $1/\rho$
--   - encoding: the pre-filtered list → the Finset of surviving indices; reason: the list is explicit; an index set represents it, duplicates included
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 12, p.39 (PDF p.42), with Fig. 8 (Prefilter-Candidate-List), p.39 (PDF p.42)

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_AR

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 12, p.39 (PDF p.42), with
the count of Fig. 8 (Prefilter-Candidate-List, step (1): "t = (1/ρ) log_q(L/ε)", rounded up to an
integer): "Let
T = {T¹, …, T^L} be a list of L explicitly given trilinear forms over 𝔽_q^n. Let f ∈ T be a hidden
trilinear form accessible only via an evaluation oracle. Given an analytic rank bound ρ and a
failure parameter ε ∈ (0, 1), there exists a randomized algorithm that pre-filters the list T
such that: (i) it makes at most O_q((log L)/ρ + (1/ρ) log(1/ε)) quantum queries to f; and (ii)
with probability at least 1 − ε, every surviving trilinear form Tⁱ in the list satisfies
AR(f − Tⁱ) ≤ ρ."

**Formalization Note.** The algorithm depends on the list, `ρ` and `ε`, not on the hidden index
`k`; it outputs the set of surviving indices. Corrections and readings (see the item's
differences): the count is Fig. 8's `t`, rounded up: `⌈log_q(L/ε)/ρ⌉` (the O-form is false for large `ρ`), and the
success event adds "every index `i` with `Tⁱ = f` survives" ("The true form always survives",
p.6, PDF p.9), without which (ii) is satisfied by the empty output. -/
theorem lemma_12 {F : Type} [Field F] [Fintype F] [DecidableEq F] (n L : ℕ)
    (T : Fin L → TriForm F n) (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ A : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F (Finset (Fin L)), ∀ k : Fin L,
      A.maxQueries (oracle (T k)) ≤ ⌈Real.logb (Fintype.card F) (L / ε) / ρ⌉₊ ∧
      1 - ε ≤ A.outProb (oracle (T k))
        (fun S => (∀ i, T i = T k → i ∈ S) ∧ ∀ i ∈ S, AR (T k - T i) ≤ ρ) := by sorry

end TriFormQ
