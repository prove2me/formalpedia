-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_lemma_3_10
-- name    : QAdvFew.PoQOracle.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:44.635445+00:00
-- url     : https://prove2.me/theorems/2a5be334-8a7a-4747-ad93-8da6802ff1b2
-- title:
--   Lemma 3.10 — hardness of Forrelation
-- statement:
--   There is a family of distributions $\mathcal F_N$ on $\{0,1\}^N$ (Forrelation, Theorem 1.2 of [RT19]) such that:
--
--   1. a quantum algorithm $\mathcal A$ making $\mathrm{polylog}(N)$ queries to its input and running in time $\mathrm{polylog}(N)$ satisfies
--   $$\Bigl|\Pr_{x\leftarrow\mathcal F_N}[\mathcal A(x)\to1]-\Pr_{x\leftarrow\{0,1\}^N}[\mathcal A(x)\to1]\Bigr|\ge1-\frac1{N^2};$$
--   2. every $C\in\mathsf{AC}^0(\mathrm{quasipoly}(N),O(1))$ satisfies
--   $$\Bigl|\Pr_{x\leftarrow\mathcal F_N}[C(x)\to1]-\Pr_{x\leftarrow\{0,1\}^N}[C(x)\to1]\Bigr|\le\frac{\mathrm{polylog}(N)}{\sqrt N}.$$
--
--   This is the separation that makes the oracle part $B$ visible to quantum algorithms and invisible to classical ones.
--
--   Differences from the source:
--   - reading: an explicit distribution → existence of a family F; reason: the paper never gives the construction and uses only properties (1) and (2)
--   - reading: polylog(N), quasipoly(N), O(1) → one constant c with c(log₂N+1)^c, every k with 2^{(log₂N+1)^k}, every depth d, with c chosen after k and d; reason: the bare (log N)^c without a factor is false at N = 2
--   - generalization: C(x) → C(x, z) with z from any independent distribution on any length; reason: the note under the lemma on p. 14; the printed bound is the case m = 0
--   - encoding: a quantum algorithm with input x, for every N → a family of oracle circuits generated in time polynomial in log N, reading x through forrOracle; N ≥ 1; reason: x is accessed by queries, and uniformity is what running in time polylog(N) means; 1/N² is undefined at N = 0
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 3.10, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_ForrQuantum
import Definitions.Def_QAdvFew_PoQOracle_ForrAC0

namespace QAdvFew.PoQOracle

/-- **Lemma 3.10 (Hardness of Forrelation, Theorem 1.2 of [RT19])** (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 3.10, p. 14
(PDF p. 16)). There is a family of distributions `F_N` on `{0,1}^N` such that (1) a quantum
algorithm with `polylog(N)` queries and time distinguishes `F_N` from uniform with advantage
`≥ 1 − 1/N²`, and (2) every `AC0(quasipoly(N), O(1))` circuit, even given extra input independent
of `x`, distinguishes them with advantage `≤ polylog(N)/√N`.

**Formalization Note** "Explicit" is read as existence (the paper never uses the construction, only
properties (1) and (2)). The asymptotic terms take the uniform forms of `ForrQuantum` and `ForrAC0`;
`N ≥ 1`. -/
theorem lemma_3_10 : ∃ F : (N : ℕ) → PMF (Fin N → Bool), ForrQuantum F ∧ ForrAC0 F := by sorry

end QAdvFew.PoQOracle
