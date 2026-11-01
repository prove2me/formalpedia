-- Prove2me | Theorems.Thm_WildeQIT_HSW_theorem_20_3_1
-- name    : WildeQIT.HSW.theorem_20_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:15:56.160999+00:00
-- url     : https://prove2.me/theorems/b1b87174-8018-4298-83ad-1f81125ad500
-- title:
--   Theorem 20.3.1 (Holevo–Schumacher–Westmoreland): $C(\mathcal N) = \chi_{\mathrm{reg}}(\mathcal N) = \lim_k \frac1k\chi(\mathcal N^{\otimes k})$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel between finite-dimensional Hilbert spaces. The classical capacity of $\mathcal N$ equals the regularization of its Holevo information:
--
--   $$
--   C(\mathcal N) = \chi_{\mathrm{reg}}(\mathcal N), \qquad \chi_{\mathrm{reg}}(\mathcal N) \equiv \lim_{k\to\infty}\frac1k\,\chi(\mathcal N^{\otimes k}),
--   $$
--
--   where
--
--   1. $C(\mathcal N)$ is the supremum of the achievable rates of classical communication, a rate $C$ being achievable when for every $\delta>0$, $\varepsilon\in(0,1)$ and all sufficiently large $n$ there is a code with $n$ channel uses, rate at least $C-\delta$ and maximal error probability at most $\varepsilon$; codewords may be entangled across the channel inputs and the decoder is any POVM on all $n$ outputs;
--   2. $\chi(\mathcal N) = \max I(X;B)_\rho$ is the Holevo information of the channel, maximized over classical–quantum states $\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\psi^x)$ with pure inputs $\psi^x$.
--
--   The statement includes that the limit defining $\chi_{\mathrm{reg}}(\mathcal N)$ exists. It is the quantum generalization of Shannon's channel coding theorem; when $\chi$ is additive for $\mathcal N$ (for example for entanglement-breaking channels) it reduces to $C(\mathcal N) = \chi(\mathcal N)$.
--
--   **Formalization Note** The channel is the published `WildeQIT.QChannel` in Choi–Kraus form, and $\mathcal N^{\otimes k}$ acts on operators indexed by functions $\{1,\dots,k\}\to A$. Logarithms are base 2. The statement asserts that the set of achievable rates is bounded above (implied by the book's equality with a real number; Lean's supremum of an unbounded set would be the junk value $0$), and that $\frac1k\chi(\mathcal N^{\otimes k})$ converges to $C(\mathcal N)$ as $k\to\infty$.
--
--   Differences from the source:
--   - encoding: C(N) = lim_k (1/k) χ(N^⊗k), the limit assumed to exist → the set of achievable rates is bounded above and (1/k) χ(N^⊗k) tends to C(N); reason: convergence to C(N) is the book's equation including existence of the limit, and boundedness rules out Lean's junk value sSup = 0 of an unbounded set; both follow from the book's equality with a real number
--   - reading: an (n, C − δ, ε) code, i.e. rate (1/n) log |M| = C − δ (p. 562) → a code with M ≥ 1 messages and rate (1/n) log₂ M ≥ C − δ; reason: the number of messages |M| is an integer, so a rate of exactly C − δ is in general unavailable; discarding messages keeps the maximal error, so "at least" is the standard reading and gives the same supremum
--   - encoding: χ(N) maximized over classical–quantum states on an arbitrary finite alphabet (20.8) → sSup over alphabets {0, …, k−1}, k ∈ ℕ; reason: the mutual information is invariant under relabelling the alphabet
--   - encoding: a quantum channel (linear CPTP map) → WildeQIT.QChannel in Choi–Kraus form, N^⊗k by product Kraus operators; reason: in finite dimensions the two describe the same maps (Choi–Kraus theorem)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 20.3.1, (20.22)–(20.23), p. 564; (20.8), p. 561; §20.2.1, p. 562

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_HSW_tensorPowMap
import Definitions.Def_WildeQIT_HSW_holevoInfo
import Definitions.Def_WildeQIT_HSW_IsAchievableRate
import Definitions.Def_WildeQIT_HSW_classicalCapacity

open Filter Topology

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 20.3.1
(Holevo–Schumacher–Westmoreland), p. 564: "The classical capacity of a quantum channel is equal
to the regularization of the Holevo information of the channel: C(N) = χ_reg(N), (20.22) where
χ_reg(N) ≡ lim_{k→∞} (1/k) χ(N^⊗k), (20.23) and the Holevo information χ(N) of a channel N is
defined in (20.8)."

**Formalization Note.** Finite-dimensional Hilbert spaces are finite index types and the
channel is a published `WildeQIT.QChannel A B` (Choi–Kraus form). `N^⊗k` is
`WildeQIT.HSW.tensorPowMap N k`, `χ` is `WildeQIT.HSW.holevoInfo` (the pure-state form (20.8)),
and `C(N)` is `WildeQIT.HSW.classicalCapacity N`, the supremum of the rates
`WildeQIT.HSW.IsAchievableRate` (maximal error, codewords possibly entangled across channel
uses, a collective POVM on `Bⁿ`; §20.2.1). The limit is part of the statement: the sequence
`(1/k) χ(N^⊗k)` converges, and its limit is `C(N)`. Since `sSup` of a set unbounded above is
`0` in Lean, the statement also asserts that the achievable rates are bounded above, which the
book's equality with a real number implies. Logarithms are base 2. -/
theorem theorem_20_3_1 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : WildeQIT.QChannel A B) :
    BddAbove {C : ℝ | IsAchievableRate N C} ∧
      Tendsto (fun k : ℕ => holevoInfo (tensorPowMap N k) / k) atTop
        (𝓝 (classicalCapacity N)) := by sorry

end WildeQIT.HSW
