-- Prove2me | Theorems.Thm_PHIP1781_comparison_det_pos
-- name    : PHIP1781.comparison_det_pos
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:34:38.877195+00:00
-- url     : https://prove2.me/theorems/bd036564-727a-49ef-b0d3-c2aef6c9c449
-- title:
--   comparison det pos — PHIP1781
-- statement:
--   Para a matriz racional
--   $$ M=\begin{pmatrix}1&-1/10\\-1/10&2/5\end{pmatrix}, $$
--   vale \(\det M>0\). A afirmação se limita a esta matriz explícita.
--
--   Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Inventário documental V3, PF28 FINAL 15/11/2026. PHIP1781.comparison_det_pos; fonte PHIP-1781_Astra_Fable_pacote_c_9_recuperado_Z_J_0_256678_certificado_e_E_indefinido_BSS_com_margem_do_3fe98395_block5.lean; SHA256 original cd274aebcf793557a25dd499830e44491300c5d53d12fea5d07ad236e1d7fc94. Sem reivindicação de novidade.

import Mathlib
open Filter Topology

theorem PHIP1781.comparison_det_pos : 0 < Matrix.det (!![1, -(1/10); -(1/10), 2/5] : Matrix (Fin 2) (Fin 2) ℚ) := by sorry
