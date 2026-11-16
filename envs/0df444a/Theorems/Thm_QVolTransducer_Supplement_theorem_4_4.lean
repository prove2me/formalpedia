-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_4_4
-- name    : QVolTransducer.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:40:53.424599+00:00
-- url     : https://prove2.me/theorems/5d008998-f0c4-4d97-a21a-164448976e52
-- title:
--   Theorem 4.4 — the transducer $T=A^\dagger(U\oplus I)A$ reflects through the stationary state of an electrical network
-- statement:
--   Let $(G=(V,E),r)$ be an electrical network with $R=1$, so that $\pi_v=1/r_v$; let $\mathcal H=(\mathbb C^V)^{\otimes2}$, $U=(2\Pi_{H_1}-I)(2\Pi_{H_2}-I)$ the transducer of Lemma 4.3,
--
--   $$A=(H\otimes I_{\mathcal H})\big(I_{\mathcal H}\oplus(2\Pi_{H_1}-I_{\mathcal H})\big)(H\otimes I_{\mathcal H}),\quad H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad T=A^\dagger(U\oplus I_{\mathcal H})A.$$
--
--   Then $T$ is a transducer with public space $\mathcal H$ and private space $\mathcal H$, and
--
--   1. $N|\pi\rangle\overset{T}{\rightsquigarrow}N|\pi\rangle$ with catalyst $0$ and complexity $W(U,|\pi\rangle)=0$;
--   2. $N|\bar\pi\rangle\overset{T}{\rightsquigarrow}-N|\bar\pi\rangle$ with catalyst $\Pi_{H_1^\perp}|f^{\bar\pi}\rangle$ and complexity
--   $$W(U,|\bar\pi\rangle)=2R_{\mathrm{eff}}(G,r;\bar\pi)-\||\bar\pi\rangle\|^2$$
--   for every net-flow $\bar\pi\in\mathbb C^V$ ($\sum_v\bar\pi_v=0$),
--
--   where $|\pi\rangle=\sum_v\sqrt{\pi_v}|v\rangle$, $|\bar\pi\rangle=\sum_v\bar\pi_v/\sqrt{\pi_v}\,|v\rangle$, $N|v\rangle=|v\rangle|*_v\rangle$ and $f^{\bar\pi}$ is the minimum-energy flow with net-flow $\bar\pi$.
--
--   Unlike Lemma 4.3, the public and private spaces of $T$ do not depend on the star states, so $T$ can be made canonical: it depends on the network only through three reflections through $H_1$.
--
--   **Formalization Note** "Transducer" includes unitarity of $T$. The printed complexity $W(U,\cdot)$ is asserted both for Lemma 4.3's $U$ (public space $H_1$, private space $H_1^\perp$) and for $T$; the minimum-energy flow is asserted to exist, and the catalyst identities hold for every minimum-energy flow.
--
--   Differences from the source:
--   - encoding: graph G = (V, E) with self-loops, resistance r : E → ℝ>0, flows f : E → ℂ with an arbitrary orientation → a symmetric Boolean adjacency, a symmetric resistance function, and flows as antisymmetric functions F(v, w) = −F(w, v) supported on edges; reason: orientation-free encoding of the same flows; a self-loop carries no net-flow and only adds energy, so minimum-energy flows and R_eff are unchanged
--   - reading: 'T is a transducer' → T is unitary (Matrix.unitaryGroup), and its transductions are TransducesWith; reason: Definition 2.7: a transducer is a unitary
--   - reading: complexity W(U, |π⟩) = 0 and W(U, |π̄⟩) = 2R_eff − ‖|π̄⟩‖², written with Lemma 4.3's U in a statement about T → both W of Lemma 4.3's U (public H₁, private H₁^⊥) on N|·⟩ and W(T, N|·⟩) equal the printed values; reason: the printed symbol U is ambiguous in a theorem about T; both quantities equal the printed values, so both readings are asserted
--   - encoding: the minimum-energy flow f^π̄ → a minimum-energy flow exists, and the catalyst statements hold for every minimum-energy flow; reason: the minimum-energy flow is unique; this states the same without choosing it
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 4.4, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_transductionComplexity
import Definitions.Def_QVolTransducer_starState
import Definitions.Def_QVolTransducer_Supplement_ElecNetwork

namespace QVolTransducer.Supplement

open QAlgorithms

/-- **Transducer reflecting through the stationary state of an electrical network**
(Cornelissen, Apers, Gribling, *Improved quantum volume estimation with transducers and amortized
quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 4.4, p.30
(PDF p.32)).

Let `(G = (V, E), r)` be an electrical network with `R = 1`, `H = (ℂ^V)^{⊗2}`,
`U = (2Π_{H_1} − I)(2Π_{H_2} − I)` the transducer of Lemma 4.3,
`A = (H ⊗ I_H)(I_H ⊕ (2Π_{H_1} − I_H))(H ⊗ I_H) ∈ U(H^{⊕2})` with the Hadamard
`H = (1/√2)[[1, 1], [1, −1]]`, and `T = A†(U ⊕ I_H)A`. Then `T` is a transducer with public space
`H` and private space `H`, and
1. `N|π⟩ ⇝_T N|π⟩` with catalyst `0` and complexity `W(U, |π⟩) = 0`;
2. `N|π̄⟩ ⇝_T −N|π̄⟩` with catalyst `Π_{H_1^⊥}|f^π̄⟩` and complexity
   `W(U, |π̄⟩) = 2R_eff(G, r; π̄) − ‖|π̄⟩‖²`, for every net-flow `π̄ ∈ ℂ^V`,
where `|π⟩ = Σ_v √π_v |v⟩`, `|π̄⟩ = Σ_v π̄_v/√π_v |v⟩`, `π_v = 1/r_v`, `N|v⟩ = |v⟩|∗_v⟩` and
`f^π̄` is the minimum-energy flow with net-flow `π̄`.

**Formalization Note** `T` is a matrix on `ℂ^((V×V) ⊕ (V×V))` (public summand first); "transducer"
includes that `T` is unitary. The complexity printed as `W(U, ·)` is stated twice: for Lemma 4.3's
`U` with public space `H_1` and private space `H_1^⊥` (`lemma43Complexity`), and for `T` itself
(the published `transductionComplexity`); both readings are asserted. The minimum-energy flow is
asserted to exist, and the catalyst identities are asserted for every minimum-energy flow. Flows are
antisymmetric functions on vertex pairs (no orientation is chosen); `R_eff` uses the energy
`Σ_e |f_e|² r_e` of Definition 2.23, while `|f⟩` is the embedding of Lemma 4.2. -/
theorem theorem_4_4 {V : Type} [Fintype V] [DecidableEq V] (G : ElecNetwork V)
    (hR : G.totalR = 1) :
    G.Top ∈ Matrix.unitaryGroup ((V × V) ⊕ (V × V)) ℂ ∧
    TransducesWith G.Top (G.Nmap (sqrtVec G.stat)) (G.Nmap (sqrtVec G.stat)) 0 ∧
    transductionComplexity G.Top (G.Nmap (sqrtVec G.stat)) = 0 ∧
    G.lemma43Complexity (sqrtVec G.stat) = 0 ∧
    ∀ πbar : V → ℂ, ∑ v, πbar v = 0 →
      (∃ F, G.IsMinEnergyFlow F πbar) ∧
      ∀ F, G.IsMinEnergyFlow F πbar →
        TransducesWith G.Top (G.Nmap (flowVec G.stat πbar)) (-G.Nmap (flowVec G.stat πbar))
          (G.flowEmbed F - act G.proj1 (G.flowEmbed F)) ∧
        ‖G.flowEmbed F - act G.proj1 (G.flowEmbed F)‖ ^ 2 =
          2 * G.effRes πbar - ‖flowVec G.stat πbar‖ ^ 2 ∧
        transductionComplexity G.Top (G.Nmap (flowVec G.stat πbar)) =
          2 * G.effRes πbar - ‖flowVec G.stat πbar‖ ^ 2 ∧
        G.lemma43Complexity (flowVec G.stat πbar) =
          2 * G.effRes πbar - ‖flowVec G.stat πbar‖ ^ 2 := by sorry

end QVolTransducer.Supplement
