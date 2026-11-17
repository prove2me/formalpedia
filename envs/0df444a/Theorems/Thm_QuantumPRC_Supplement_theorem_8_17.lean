-- Prove2me | Theorems.Thm_QuantumPRC_Supplement_theorem_8_17
-- name    : QuantumPRC.Supplement.theorem_8_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:39:43.061676+00:00
-- url     : https://prove2.me/theorems/5bb20666-3bc1-4cf8-bb1d-0ae39fa67fd9
-- title:
--   Theorem 8.17 — keyed CWS codes from classical codes correct $t(n_P)$-local noise on average over the key
-- statement:
--   Fix a constant $p>0$. Let $n_P=2n$ range over even numbers and $n_L=n_L(n_P)$. Let $t$ satisfy
--
--   $$
--   t(n_P)=o\Big(\frac{n_P\log\log n_P}{\log n_P}\Big). \tag{248}
--   $$
--
--   Let $C:\{0,1\}^{n_L}\to\{0,1\}^{n_P}$ be an injective encoder with a deterministic decoder $D$, both computable in time polynomial in $n_P$, such that
--
--   $$
--   D(C(x)\oplus e)=x\qquad\text{for all }x\in\{0,1\}^{n_L},\ e\in\{0,1\}^{n_P}\text{ with }\mathrm{wt}(e)\le p\,n_P/2, \tag{249}
--   $$
--
--   and let (GraphSample, Recover) be algorithms with the guarantees of Theorem 7.1 for the constant $p$, run at radius $t(n_P)$. Then Construction 8.16 corrects $t(n_P)$-local noise on average over the key: for every family $\{\mathcal E_{n_P}\}$ of $t(n_P)$-local noise channels (Definition 3.7), independent of the key,
--
--   $$
--   \Big\|\mathop{\mathbb E}_{\mathsf{sk}\leftarrow\mathrm{KeyGen}(1^{n_P})}\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_{n_P}\circ\mathrm{Enc}_{\mathsf{sk}}-\mathrm{id}_{n_L}\Big\|_\diamond\le\mathrm{negl}(n_P). \tag{252}
--   $$
--
--   The theorem turns any efficiently and exactly decodable classical code, linear or not, into an efficiently decodable keyed quantum code against local noise of nearly linear weight.
--
--   Differences from the source:
--   - generalization: (248) t(nP) = o(nP log log nP / log nP) as nP → ∞ → only along even nP: t(2n) = o(radiusScale(2n)) as n → ∞; reason: the printed hypothesis implies this one, and the construction only uses even nP
--   - generalization: GraphSample and Recover from Theorem 7.1 with constant p and radius function m ↦ t(2m) → any machines (gc, GS, Rec) with GraphRecoverSpec p gc GS Rec (the base mission's corrected form of Theorem 7.1, radius read in unary), run at radius t(2n); reason: the proof uses only properties (i) and (ii) of Theorem 7.1 at input length nP/2; the base QuantumPRC.theorem_7_1 supplies such machines for every p > 0 (SUPPLEMENT.md decision 4)
--   - encoding: nP ranges over even positive integers; nL = nL(nP); wt(e) ≤ p nP/2; negl(nP) → index n with nP = 2n; nL n; wt e ≤ p·n; a negligible function of n; reason: same instances; a function is negligible in 2n iff it is negligible in n
--   - encoding: C and D computable in time polynomial in nP → IsPolyFamily C and IsPolyFamily D (one polynomial-time machine reading 1^n and the input); reason: the base model of deterministic polynomial-time families
--   - encoding: û = Recover(G, e) → the first 2n bits of Rec(1^{t(2n)}, GS-output code of G, e), false beyond the end; reason: GraphRecoverSpec promises a 2n-bit output on the relevant inputs; the sampler's output code is the adjacency code of G whenever it is valid, which the spec guarantees
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 8.17, Eq. (252), p.64; §8.5, Eqs. (248)-(249), p.63; Construction 8.16, p.64; Theorem 7.1, p.40

import Mathlib
import Definitions.Def_QuantumPRC_Supplement_C816
import Definitions.Def_QuantumPRC_IsLocalNoise

open Filter Asymptotics

namespace QuantumPRC.Supplement

/-- **Theorem 8.17** (keyed CWS codes from classical codes). Hsieh, Yamada, *Quantum Pseudorandom
Error-Correcting Codes*, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d…), Theorem 8.17,
p.64: "Under the assumptions above, Construction 8.16 encodes `nL` qubits into `nP` qubits and corrects
`t(nP)`-local quantum noise on average over the key. More precisely, for every family `{E_{nP}}` of
`t(nP)`-local noise channels independent of the key,
`‖𝔼_{sk←KeyGen(1^{nP})} Dec_sk ∘ E_{nP} ∘ Enc_sk − id_{nL}‖⋄ ≤ negl(nP)`. (252)"
Assumptions of §8.5, p.63: `p > 0` constant; `nP` even; `t(nP) = o(nP log log nP / log nP)` (248);
`C` injective with a deterministic decoder `D`, both polynomial-time, with `D(C(x) ⊕ e) = x` whenever
`wt(e) ≤ p nP/2` (249); GraphSample and Recover from Theorem 7.1 with constant `p` and radius `m ↦ t(2m)`.

**Formalization Note.**
* Indexing by `n` with `nP = 2n`, so `p nP/2 = p n` and `negl(nP)` is `negl(n)`.
* (248) is assumed only along even `nP` (`t(2n) = o(radiusScale(2n))`), which the printed hypothesis
  implies.
* GraphSample and Recover are any machines `(gc, GS, Rec)` satisfying `GraphRecoverSpec p` (the base
  mission's form of Theorem 7.1, with the radius `t(2n)` passed in unary); the base mission's Theorem
  7.1 (`QuantumPRC.theorem_7_1`) provides such a triple for every `p > 0`.
* Recover reads the sampler's output code of `G`.
* The noise family `E` is arbitrary and fixed before the key, and the negligible function is chosen
  after `E`. -/
theorem theorem_8_17 (p : ℝ) (hp : 0 < p) (K : C816)
    (ht : (fun n => (K.t (2 * n) : ℝ)) =o[atTop] (fun n => radiusScale (2 * n)))
    (hCinj : ∀ n, Function.Injective (K.C n))
    (hCD : ∀ n (x : Bits (K.nL n)) (e : Bits (2 * n)), (wt e : ℝ) ≤ p * n →
      K.D n (xorB (K.C n x) e) = x)
    (hCpoly : IsPolyFamily K.C (fun _ x => [bits x]) (fun _ y => bits y))
    (hDpoly : IsPolyFamily K.D (fun _ y => [bits y]) (fun _ x => bits x))
    (hspec : GraphRecoverSpec p K.gc K.GS K.Rec)
    (E : ∀ n, WildeQIT.QChannel (Bits (2 * n)) (Bits (2 * n)))
    (hE : IsLocalNoise (fun n => K.t (2 * n)) (fun n => 2 * n) E) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n, diamondDist (K.avgDecNEnc n (E n).apply) id ≤ ν n := by sorry

end QuantumPRC.Supplement
