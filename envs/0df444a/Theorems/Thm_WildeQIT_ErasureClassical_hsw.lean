-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_hsw
-- name    : WildeQIT.ErasureClassical.hsw
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:44.815854+00:00
-- url     : https://prove2.me/theorems/842efc57-9c60-4847-a9e0-401440d3a39c
-- title:
--   Theorem 20.3.1 (Holevo–Schumacher–Westmoreland): $C(\mathcal N)=\chi_{\rm reg}(\mathcal N)$
-- statement:
--   Let $\mathcal N$ be a quantum channel between finite-dimensional systems. The classical capacity of $\mathcal N$ equals the regularization of its Holevo information:
--
--   $$
--   C(\mathcal N)=\chi_{\rm reg}(\mathcal N),\qquad \chi_{\rm reg}(\mathcal N)\equiv\lim_{k\to\infty}\frac1k\,\chi(\mathcal N^{\otimes k}),
--   $$
--
--   where $\chi$ is the Holevo information (20.8) and $C(\mathcal N)$ is the supremum of the rates achievable by codes with vanishing maximal error probability, with encoders entangled across channel uses and collective decoding measurements.
--
--   This is the classical capacity theorem; for the erasure channel it reduces the computation of $C(\mathcal N^\varepsilon)$ to bounding $\chi((\mathcal N^\varepsilon)^{\otimes n})$.
--
--   **Formalization Note** The statement asserts that the limit exists as a real number $L$ and that the operational capacity equals $L$. The channel is in Kraus form with a nonempty input space. Logarithms are base 2.
--
--   Differences from the source:
--   - reading: χreg(N) ≡ lim_{k→∞} (1/k) χ(N^⊗k), used as a number → the limit exists as a real number L and C(N) = L; reason: the definition (20.23) presupposes that the limit exists; the statement makes that presupposition explicit
--   - encoding: a quantum channel → a Kraus-form channel with a nonempty finite input index type; C(N) in EReal; reason: the book's Hilbert spaces are finite-dimensional and nonzero; every channel has a Kraus form (Theorem 4.4.1); the supremum in EReal is the least upper bound without a boundedness hypothesis
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 20.3.1, (20.22)–(20.23), p. 564

import Definitions.Def_WildeQIT_ErasureClassical_classicalCapacity
import Definitions.Def_WildeQIT_ErasureClassical_holevoInfo
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Topology

namespace WildeQIT.ErasureClassical

/-- **Theorem 20.3.1 (Holevo–Schumacher–Westmoreland)** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, p. 564): "The classical capacity of a quantum channel is
equal to the regularization of the Holevo information of the channel: `C(N) = χreg(N)` (20.22),
where `χreg(N) ≡ lim_{k→∞} (1/k) χ(N^{⊗k})` (20.23), and the Holevo information `χ(N)` of a
channel `N` is defined in (20.8)."

**Formalization Note.** The statement asserts that the limit (20.23) exists (as a real number
`L`) and that the operational capacity of §20.2.1 equals it. The channel is any channel in Kraus
form between finite-dimensional spaces (every channel has this form, Theorem 4.4.1); the input
space is nonempty (a Hilbert space of dimension at least one). -/
theorem hsw {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [Nonempty a]
    (N : QChannel a b) :
    ∃ L : ℝ, Tendsto (fun k : ℕ => holevoInfo (WildeQIT.Degradable.tensorPower N k) / k) atTop (𝓝 L) ∧
      classicalCapacity N = (L : EReal) := by sorry

end WildeQIT.ErasureClassical
