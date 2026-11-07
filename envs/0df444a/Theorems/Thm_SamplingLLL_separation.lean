-- Prove2me | Theorems.Thm_SamplingLLL_separation
-- name    : SamplingLLL.separation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:37.687192+00:00
-- url     : https://prove2.me/theorems/32899d75-9420-4aa2-8b43-7b34fa966b43
-- title:
--   Appendix G, p.67 — separation of terminal transcripts
-- statement:
--   At a terminal transcript of the task $(S,c)$, every member of $F_1$ is adjacent to an uncertified singleton component of $H[Y]$; no member of $R$ is adjacent to $F_1$ or to $Y$; consequently the transcript is separated with $W_t=\mathrm{vbl}(Y)\cup\mathrm{vbl}(F_1)$, $E_t=\{$every member of $Y$ is bad and every member of $F_1$ is good$\}$, $R_t=R$, and $D_t$ enumerates $S\setminus R$.
--
--   Differences from the source:
--   - encoding: separation of a positive-mass transcript → separation stated for every transcript; reason: it holds for all, and positive-mass ones are a subset; no hypothesis is added
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 2.6, p.67

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

namespace SamplingLLL

/-- Appendix G, p.67: every terminal transcript of the search is separated with `W_t = vbl(Y) ∪ vbl(F1)`,
`E_t = {every member of Y is bad, every member of F1 is good}`, `R_t = R`. Every member of `F1` is adjacent to
an uncertified singleton component of `H[Y]`; no member of `R` is adjacent to `F1` or to `Y`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 2.6, p.67. -/
theorem separation {n m : ℕ} (I : AtomicCSP n m) (G : Finset (Fin m)) (x : Fin m → ℚ)
    (S : Finset (Fin m)) (c : Fin m) (hc : c ∉ S) (t : Leaf m)
    (ht : t ∈ (I.sllData G x).leavesOf S c) :
    (∀ d ∈ I.F1 S c t, ∃ a ∈ t.1, I.comp t.1 a = {a} ∧ a ∉ G ∧ I.H.Adj a d) ∧
    (∀ r ∈ I.R S c t, ∀ d ∈ I.F1 S c t, ¬ I.H.Adj d r) ∧
    (∀ r ∈ I.R S c t, ∀ y ∈ t.1, ¬ I.H.Adj y r) ∧
    (I.sllData G x).Separated S c t := by sorry

end SamplingLLL
