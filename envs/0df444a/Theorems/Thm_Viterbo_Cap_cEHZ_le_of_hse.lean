-- Prove2me | Theorems.Thm_Viterbo_Cap_cEHZ_le_of_hse
-- name    : Viterbo.Cap.cEHZ_le_of_hse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:34.770364+00:00
-- url     : https://prove2.me/theorems/4ed8cca9-d779-4975-92e0-d0b8806d04fb
-- title:
--   The Ekeland–Hofer–Zehnder capacity is monotone under symplectic embeddings of convex domains
-- statement:
--   Let $n\ge1$ and let $K,L\subseteq\mathbb R^{2n}$ be convex domains (`Viterbo.IsConvexDomain`: bounded, convex, nonempty interior) such that $K$ embeds symplectically into $L$ (`OAI.SymmetricPolar.HasSymplecticEmbedding K L`: a map smooth on $K$, a topological embedding of $K$, mapping $K$ into $L$, whose derivative at every point of $K$ preserves $\omega_0$). Then $c_{\rm EHZ}(K)\le c_{\rm EHZ}(L)$, with $c_{\rm EHZ}$ = `Viterbo.cEHZ`, the infimum of $|A(\gamma)|$ over nonconstant generalized closed characteristics on the boundary.
--
--   This is the symplectic invariance of $c_{\rm EHZ}$ on convex domains (Hofer–Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, ch. 3, via $c_{\rm HZ}=c_{\rm EHZ}$ on convex domains). It is what makes the Viterbo mission's capacity statement (Haim-Kislev–Ostrover, p. 2) hold: the envelope $U\mapsto\sup\{c_{\rm EHZ}(K): K\hookrightarrow U\}$ is then a symplectic capacity agreeing with $c_{\rm EHZ}$ on convex domains.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, monotonicity of the Ekeland–Hofer–Zehnder capacity under symplectic embeddings of convex domains, used in the capacity statement, cf. Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3

import Mathlib
import Definitions.Def_Viterbo

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal

namespace Viterbo.Cap

theorem cEHZ_le_of_hse {n : ℕ} (hn : 1 ≤ n) {K L : Set (Phase n)} (hK : IsConvexDomain K)
    (hL : IsConvexDomain L) (he : HasSymplecticEmbedding K L) : cEHZ K ≤ cEHZ L := by
  sorry

end Viterbo.Cap
