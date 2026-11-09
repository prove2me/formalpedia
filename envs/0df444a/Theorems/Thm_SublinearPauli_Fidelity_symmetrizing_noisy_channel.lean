-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_symmetrizing_noisy_channel
-- name    : SublinearPauli.Fidelity.symmetrizing_noisy_channel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:49:43.997481+00:00
-- url     : https://prove2.me/theorems/512e5d30-54fe-4082-8559-a599fafc5a45
-- title:
--   Lemma 3 — $\mathrm{BSC}_p^{\otimes2}\succeq C$ for $p\le(7-\sqrt{33})/16$
-- statement:
--   Let $p$ be a real number with $p\le\frac{7-\sqrt{33}}{16}$. Then, in the Loewner order,
--   $$\mathrm{BSC}_p^{\otimes2}\succeq C=\begin{pmatrix}\tfrac34&0&0&\tfrac14\\0&\tfrac34&0&\tfrac14\\0&0&\tfrac34&\tfrac14\\\tfrac14&\tfrac14&\tfrac14&\tfrac14\end{pmatrix},\qquad \mathrm{BSC}_p=\begin{pmatrix}1-p&p\\p&1-p\end{pmatrix},$$
--   that is, $\mathrm{BSC}_p^{\otimes 2}-C$ is positive semidefinite, where $C$ is indexed by the letters $X,Y,Z,I$ and these are identified with the two-bit index of $\mathrm{BSC}_p^{\otimes2}$ by $I=00$, $X=10$, $Z=01$, $Y=11$.
--
--   At $p^*=\frac{7-\sqrt{33}}{16}$ one has $1-2p^*=\lambda=\frac{1+\sqrt{33}}8$; tensoring the comparison over $N$ qubits lets the Pauli graph be bounded by the Bonami–Beckner operator $T_\lambda$ on $2N$ bits.
--
--   **Formalization Note** The matrices are real; the Loewner order is positive semidefiniteness of the difference, not an entrywise comparison. The statement covers every real $p\le p^*$, as printed, including $p<0$.
--
--   Differences from the source:
--   - encoding: $C$ in the row and column order $X,Y,Z,I$ against $\mathrm{BSC}_p^{\otimes2}$ indexed by two bits → $C$ transported by the bit-pair labeling $I=00$, $X=10$, $Z=01$, $Y=11$; reason: the paper leaves the identification implicit, and the inequality holds for one bijection iff for all (symmetries of both matrices act transitively on the bijections).
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.14, Lemma 3 (restated and proved in §7, pp.17–19)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_NoisyChannel

namespace SublinearPauli.Fidelity

/-- **Lemma 3** (Symmetrizing noisy channel), p.14 (proof §7, pp.17–19). For every real
`p ≤ (7 − √33)/16`, `BSC_p^{⊗2} ⪰ C` in the Loewner order: `BSC_p^{⊗2} − C` is positive
semidefinite, with `C` indexed by `{0,1}²` through the bit-pair labeling of the Pauli letters. -/
theorem symmetrizing_noisy_channel (p : ℝ) (hp : p ≤ (7 - Real.sqrt 33) / 16) :
    (bsc2 p - channelCBits).PosSemidef := by sorry

end SublinearPauli.Fidelity
