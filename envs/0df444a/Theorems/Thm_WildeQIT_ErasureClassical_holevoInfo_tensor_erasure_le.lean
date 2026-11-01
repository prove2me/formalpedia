-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_holevoInfo_tensor_erasure_le
-- name    : WildeQIT.ErasureClassical.holevoInfo_tensor_erasure_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:55.231965+00:00
-- url     : https://prove2.me/theorems/6eceaa21-fb15-4146-858f-83e4df8492ed
-- title:
--   Proof of Theorem 20.4.2, (20.90)–(20.97): $\chi(\mathcal M\otimes\mathcal N^\varepsilon)\le\chi(\mathcal M)+(1-\varepsilon)\log d$
-- statement:
--   Let $\mathcal M_{A_1\to B_1}$ be any quantum channel between finite-dimensional systems, and let $\mathcal N^\varepsilon_{A_2\to B_2}$ be the $d$-dimensional erasure channel with $d\ge1$ and $\varepsilon\in[0,1]$. Then
--
--   $$
--   \chi(\mathcal M\otimes\mathcal N^\varepsilon)\;\le\;\chi(\mathcal M)+(1-\varepsilon)\log d ,
--   $$
--
--   where $\chi$ is the Holevo information of a channel (20.8), and the input ensembles of $\mathcal M\otimes\mathcal N^\varepsilon$ may be entangled across $A_1A_2$.
--
--   Adding one erasure channel to any channel raises the Holevo information by at most $(1-\varepsilon)\log d$. Iterating this gives the converse of Theorem 20.4.2.
--
--   **Formalization Note** $\mathcal M$ is in Kraus form; the joint input is the product of the two input index types. Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: the chain (20.90)–(20.97) for a state ρXA1A2 that achieves χ(M ⊗ N^ε) → the inequality χ(M ⊗ N^ε) ≤ χ(M) + (1 − ε) log₂ d between the suprema; reason: the chain's first and last terms; the attaining state is a device of the proof and is not part of the claim
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 20.4.2, (20.86)–(20.97), pp. 575–576

import Definitions.Def_WildeQIT_ErasureClassical_holevoInfo
import Definitions.Def_WildeQIT_Degradable_tensorChannel
import Definitions.Def_WildeQIT_ErasureClassical_erasureChannel

namespace WildeQIT.ErasureClassical

/-- **Proof of Theorem 20.4.2, eqs. (20.86)–(20.97)** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, pp. 575–576): for any quantum channel `M_{A₁→B₁}` and the erasure
channel `N^ε_{A₂→B₂}`, `χ(M ⊗ N^ε) ≤ χ(M) + (1 − ε) log d`.

**Formalization Note.** `M` is an arbitrary channel in Kraus form between finite-dimensional
spaces; the joint input `A₁A₂` is `a × Fin d` and may carry entangled signal states. `χ` is the
Holevo information (20.8). `ε ∈ [0, 1]`, `d ≥ 1`; logarithms base 2. -/
theorem holevoInfo_tensor_erasure_le {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (M : QChannel a b) (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    holevoInfo (WildeQIT.Degradable.tensorChannel M (erasureChannel d ε h0 h1)) ≤
      holevoInfo M + (1 - ε) * Real.logb 2 d := by sorry

end WildeQIT.ErasureClassical
