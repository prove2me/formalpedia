-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_holevoChi_erasure_uniform
-- name    : WildeQIT.ErasureClassical.holevoChi_erasure_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:50.620893+00:00
-- url     : https://prove2.me/theorems/edf5aea8-63ea-4148-971f-d2b98df8c216
-- title:
--   Proof of Theorem 20.4.2: the uniform basis ensemble gives $I(X;B)=(1-\varepsilon)\log d$
-- statement:
--   Let $d\ge1$, $\varepsilon\in[0,1]$ and let $\mathcal N^\varepsilon$ be the $d$-dimensional erasure channel. Send the ensemble $\{1/d,\ |i\rangle\}_{i=0}^{d-1}$ of computational basis states, each with probability $1/d$, through $\mathcal N^\varepsilon$. The resulting Holevo information is
--
--   $$
--   I(X;B)=H\Big(\frac1d\sum_{i}\mathcal N^\varepsilon(|i\rangle\langle i|)\Big)-\frac1d\sum_i H\big(\mathcal N^\varepsilon(|i\rangle\langle i|)\big)=(1-\varepsilon)\log d .
--   $$
--
--   By Theorem 20.3.1 this shows that the rate $(1-\varepsilon)\log d$ is achievable, the lower bound in Theorem 20.4.2.
--
--   **Formalization Note** $|i\rangle\langle i|$ is the matrix unit at $(i,i)$ on `Fin d`; $I(X;B)=H(B)-H(B|X)$ is the published `HolevoCQ.holevoChi`; logarithms are base 2.
--
--   Differences from the source:
--   - encoding: "evaluating the Holevo information" of the ensemble {1/d, |i⟩} → HolevoCQ.holevoChi of the output states N^ε(|i⟩⟨i|) and the uniform weights equals (1 − ε) log₂ d; reason: the book states the value of this evaluation in the sentence; I(X; B) = H(B) − H(B|X)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 20.4.2, p. 575

import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_WildeQIT_ErasureClassical_erasureChannel
import Mathlib.Data.Matrix.Basis

namespace WildeQIT.ErasureClassical

/-- **Proof of Theorem 20.4.2, p. 575** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8): "The rate `(1 − ε) log d` is achievable by picking the input ensemble to be
`{1/d, |i⟩}` and evaluating the Holevo information": the Holevo information `I(X; B)` of the
uniform ensemble of the basis states `|i⟩⟨i|`, `i = 0, …, d − 1`, sent through the erasure
channel `N^ε`, equals `(1 − ε) log d`.

**Formalization Note.** `|i⟩⟨i|` is `Matrix.single i i 1` on `Fin d`; `I(X; B)` is
the published `HolevoCQ.holevoChi` (`H(B) − H(B|X)`, base-2 von Neumann entropy). `ε ∈ [0, 1]`, `d ≥ 1`; logarithms base 2. -/
theorem holevoChi_erasure_uniform (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    HolevoCQ.holevoChi (fun i => (erasureChannel d ε h0 h1).apply (Matrix.single i i 1))
        (fun _ : Fin d => (1 : ℝ) / d) =
      (1 - ε) * Real.logb 2 d := by sorry

end WildeQIT.ErasureClassical
