-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_classicalCapacity_erasure
-- name    : WildeQIT.ErasureClassical.classicalCapacity_erasure
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:38:27.197862+00:00
-- url     : https://prove2.me/theorems/34f98856-bff1-4447-bb4c-56531fa2aedb
-- title:
--   Theorem 20.4.2: the classical capacity of the $d$-dimensional erasure channel is $(1-\varepsilon)\log d$
-- statement:
--   Let $d\ge1$ and $\varepsilon\in[0,1]$, and let $\mathcal N^\varepsilon$ be the $d$-dimensional quantum erasure channel $\rho\mapsto(1-\varepsilon)\rho+\varepsilon|e\rangle\langle e|$, with $|e\rangle$ orthogonal to the input space. Then its classical capacity is
--
--   $$
--   C(\mathcal N^\varepsilon)=(1-\varepsilon)\log d .
--   $$
--
--   Here $C$ is the operational classical capacity: the supremum of the rates at which classical messages can be sent over many independent uses of $\mathcal N^\varepsilon$ with maximal error probability tending to zero, allowing encoding states entangled across channel uses and collective decoding measurements.
--
--   The erasure channel is one of the few channels whose classical capacity is known exactly: the capacity equals the fraction of uses that are not erased times the capacity $\log d$ of a noiseless $d$-dimensional channel, and entangled inputs do not help.
--
--   **Formalization Note** Logarithms are base 2 (bits). The capacity is a supremum in the extended reals, and the right-hand side is the real number $(1-\varepsilon)\log_2 d$ viewed there. The channel is the Kraus-form erasure channel on `Fin d` with output `Option (Fin d)`.
--
--   Differences from the source:
--   - encoding: the d-dimensional erasure channel (20.85), d a dimension → Kraus-form channel from Fin d to Option (Fin d) with d ≥ 1 (hd : 0 < d); reason: a d-dimensional Hilbert space has d ≥ 1; on density operators the Kraus form gives exactly (1 − ε)ρ + ε|e⟩⟨e|
--   - encoding: classical capacity C(N), the supremum of achievable rates → classicalCapacity, a supremum in EReal; the right side coerced to EReal; reason: the supremum in EReal is the least upper bound with no boundedness hypothesis; same value
--   - reading: an (n, C − δ, ε) code → a code with a nonempty message set of rate (1/n) log₂|M| ≥ C − δ and every p_e(m) ≤ ε; reason: |M| is an integer, so the rate is met up to rounding; dropping messages never increases the maximal error, so the set of achievable rates is the same
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 20.4.2, p. 575

import Definitions.Def_WildeQIT_ErasureClassical_classicalCapacity
import Definitions.Def_WildeQIT_ErasureClassical_erasureChannel

namespace WildeQIT.ErasureClassical

/-- **Theorem 20.4.2 (Classical Capacity of the Erasure Channel)** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, p. 575): "The classical capacity of the
`d`-dimensional quantum erasure channel is equal to `(1 − ε) log d`."

**Formalization Note.** `classicalCapacity` is the operational capacity of §20.2.1, p. 562 (the
supremum, in `EReal`, of the rates achievable with codes of vanishing maximal error over `n`
uses, encoders possibly entangled across uses, collective POVM decoders), not the Holevo
information. The erasure channel is (20.85) on `Fin d`, with the erasure symbol as the extra
output `none`; `ε ∈ [0, 1]` as in the book and `d ≥ 1` (a `d`-dimensional input space).
Logarithms are base 2. -/
theorem classicalCapacity_erasure (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    classicalCapacity (erasureChannel d ε h0 h1) = (((1 - ε) * Real.logb 2 d : ℝ) : EReal) := by sorry

end WildeQIT.ErasureClassical
